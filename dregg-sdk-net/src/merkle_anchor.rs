//! Ingress-only Merkle anchors. Leaves commit position, topic, and a 32-byte digest.
//! Odd levels duplicate the last node. Proofs bind both index and leaf count.
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Leaf {
    pub topic: String,
    pub digest: [u8; 32],
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Proof {
    pub leaf: Leaf,
    pub leaf_index: usize,
    pub leaf_count: usize,
    pub sibling_path: Vec<[u8; 32]>,
    pub root: [u8; 32],
}
fn leaf_hash(leaf: &Leaf, index: usize, count: usize) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-anchor-leaf-v1");
    h.update(&(count as u64).to_le_bytes());
    h.update(&(index as u64).to_le_bytes());
    h.update(&(leaf.topic.len() as u64).to_le_bytes());
    h.update(leaf.topic.as_bytes());
    h.update(&leaf.digest);
    *h.finalize().as_bytes()
}
fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-anchor-node-v1");
    h.update(left);
    h.update(right);
    *h.finalize().as_bytes()
}
pub fn proofs(leaves: &[Leaf]) -> Result<Vec<Proof>, &'static str> {
    if leaves.is_empty() || leaves.len() > 4096 {
        return Err("batch-size");
    }
    let mut levels = vec![
        leaves
            .iter()
            .enumerate()
            .map(|(i, l)| leaf_hash(l, i, leaves.len()))
            .collect::<Vec<_>>(),
    ];
    while levels.last().unwrap().len() > 1 {
        let next = levels
            .last()
            .unwrap()
            .chunks(2)
            .map(|pair| node(&pair[0], pair.get(1).unwrap_or(&pair[0])))
            .collect();
        levels.push(next);
    }
    let root = levels.last().unwrap()[0];
    Ok(leaves
        .iter()
        .enumerate()
        .map(|(i, leaf)| {
            let mut index = i;
            let sibling_path = levels[..levels.len() - 1]
                .iter()
                .map(|level| {
                    let sibling = level.get(index ^ 1).unwrap_or(&level[index]);
                    index /= 2;
                    *sibling
                })
                .collect();
            Proof {
                leaf: leaf.clone(),
                leaf_index: i,
                leaf_count: leaves.len(),
                sibling_path,
                root,
            }
        })
        .collect())
}
impl Proof {
    pub fn verify(&self) -> Result<(), &'static str> {
        if self.leaf_count == 0 || self.leaf_count > 4096 || self.leaf_index >= self.leaf_count {
            return Err("index");
        }
        let mut width = self.leaf_count;
        let mut index = self.leaf_index;
        let mut hash = leaf_hash(&self.leaf, index, width);
        for sibling in &self.sibling_path {
            if width == 1 {
                return Err("path-length");
            }
            if index ^ 1 >= width && *sibling != hash {
                return Err("odd-sibling");
            }
            hash = if index % 2 == 0 {
                node(&hash, sibling)
            } else {
                node(sibling, &hash)
            };
            width = width.div_ceil(2);
            index /= 2;
        }
        if width != 1 || hash != self.root {
            return Err("root");
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn merkle_anchor_leaf_node_domains_are_not_interchangeable() {
        // Without tags these exact preimages coincide: the first 32 bytes of
        // this leaf are also a possible left child, and its digest is the right.
        let leaf = Leaf {
            topic: "12345678".into(),
            digest: [7; 32],
        };
        let mut left = [0u8; 32];
        left[..8].copy_from_slice(&1u64.to_le_bytes());
        left[16..24].copy_from_slice(&8u64.to_le_bytes());
        left[24..].copy_from_slice(leaf.topic.as_bytes());
        assert_ne!(leaf_hash(&leaf, 0, 1), node(&left, &leaf.digest));
        let mut leaf_preimage = b"dregg-anchor-leaf-v1".to_vec();
        leaf_preimage.extend_from_slice(&left);
        leaf_preimage.extend_from_slice(&leaf.digest);
        assert_eq!(
            leaf_hash(&leaf, 0, 1),
            *blake3::hash(&leaf_preimage).as_bytes()
        );
        let mut node_preimage = b"dregg-anchor-node-v1".to_vec();
        node_preimage.extend_from_slice(&left);
        node_preimage.extend_from_slice(&leaf.digest);
        assert_eq!(
            node(&left, &leaf.digest),
            *blake3::hash(&node_preimage).as_bytes()
        );
    }

    #[test]
    fn merkle_anchor_refuses_a_noncanonical_odd_sibling_even_with_its_matching_root() {
        let leaf = Leaf {
            topic: "audit".into(),
            digest: [1; 32],
        };
        let mut p = proofs(&[leaf.clone(), leaf.clone(), leaf])
            .unwrap()
            .remove(2);
        p.sibling_path[0] = [9; 32];
        let lower = node(&leaf_hash(&p.leaf, 2, 3), &p.sibling_path[0]);
        p.root = node(&p.sibling_path[1], &lower);
        assert_eq!(p.verify(), Err("odd-sibling"));
    }

    #[test]
    fn merkle_anchor_teeth() {
        let leaf = Leaf {
            topic: "audit".into(),
            digest: [42; 32],
        };
        for n in [1, 2, 3, 7] {
            let ps = proofs(&vec![leaf.clone(); n]).unwrap();
            for p in ps {
                p.verify().unwrap();
                let mut q = p.clone();
                q.leaf.digest[0] ^= 1;
                assert!(q.verify().is_err());
                let mut q = p.clone();
                q.leaf.topic.push('x');
                assert!(q.verify().is_err());
                let mut q = p.clone();
                q.leaf_index ^= 1;
                assert!(q.verify().is_err());
                let mut q = p.clone();
                q.root[0] ^= 1;
                assert!(q.verify().is_err());
                let mut q = p.clone();
                q.leaf_count += 1;
                assert!(q.verify().is_err());
                if !p.sibling_path.is_empty() {
                    let mut q = p.clone();
                    q.sibling_path[0][0] ^= 1;
                    assert!(q.verify().is_err());
                }
            }
        }
        // A digest equal to an internal node is still hashed as a leaf.
        let inner = node(&[1; 32], &[2; 32]);
        assert_ne!(
            leaf_hash(
                &Leaf {
                    topic: String::new(),
                    digest: inner
                },
                0,
                1
            ),
            inner
        );
        assert_ne!(leaf_hash(&leaf, 0, 2), leaf_hash(&leaf, 1, 2));
    }
}
