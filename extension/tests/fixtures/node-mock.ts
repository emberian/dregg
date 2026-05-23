import express from 'express';
import type { Server } from 'http';

/**
 * Mock pyana node HTTP server for deterministic testing.
 * Simulates all endpoints the extension calls.
 */

export interface MockNodeOptions {
  port?: number;
}

export interface MockNodeState {
  balance: number;
  tokens: Array<{ id: string; actions: string[]; resource: string }>;
  quota: {
    bytesStored: number;
    bytesLimit: number;
    objectCount: number;
    computronsRemaining: number;
  };
  services: Array<{ name: string; path: string; kind: string; version: number; tags: string[] }>;
  storedFiles: Map<string, string>; // hash -> base64 content
  lastSubmittedTurn: any;
  lastMountRequest: any;
  lastBearerAuth: any;
  lastPeerExchange: any;
}

export class MockNode {
  private app: express.Express;
  private server: Server | null = null;
  private port: number;
  state: MockNodeState;

  constructor(opts: MockNodeOptions = {}) {
    this.port = opts.port || 8420;
    this.state = this.defaultState();
    this.app = express();
    this.app.use(express.json());
    this.setupRoutes();
  }

  private defaultState(): MockNodeState {
    return {
      balance: 1000,
      tokens: [
        { id: 'tok_mock_001', actions: ['read', 'write'], resource: 'documents/*' },
        { id: 'tok_mock_002', actions: ['transfer'], resource: 'wallet/balance' },
      ],
      quota: {
        bytesStored: 4096,
        bytesLimit: 1048576,
        objectCount: 3,
        computronsRemaining: 500000,
      },
      services: [
        { name: 'oracle-price', path: '/services/oracle-price', kind: 'oracle', version: 1, tags: ['oracle', 'price'] },
        { name: 'storage-node', path: '/services/storage', kind: 'storage', version: 2, tags: ['storage', 'cas'] },
      ],
      storedFiles: new Map(),
      lastSubmittedTurn: null,
      lastMountRequest: null,
      lastBearerAuth: null,
      lastPeerExchange: null,
    };
  }

  private setupRoutes() {
    // Health / status endpoint.
    this.app.get('/status', (_req, res) => {
      res.json({
        ok: true,
        version: '0.1.0-mock',
        merkle_root: 'abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789',
        height: 42,
        peer_count: 3,
      });
    });

    // Wallet balance.
    this.app.get('/wallet/balance', (_req, res) => {
      res.json({ balance: this.state.balance });
    });

    // Submit a turn.
    this.app.post('/turns/submit', (req, res) => {
      this.state.lastSubmittedTurn = req.body;
      const turnId = `turn_${Date.now()}_mock`;
      res.json({ turn_id: turnId, accepted: true, receipt: 'mock_receipt_hash' });
    });

    // Bearer auth (export sturdy ref).
    this.app.post('/turns/bearer-auth', (req, res) => {
      this.state.lastBearerAuth = req.body;
      const cellId = req.body.cell_id || 'abcd'.repeat(16);
      const nodeId = 'node_mock_001';
      res.json({
        uri: `pyana://${nodeId}/${cellId}`,
        cell_id: cellId,
        node_id: nodeId,
      });
    });

    // Peer exchange (enliven URI).
    this.app.post('/turns/peer-exchange', (req, res) => {
      this.state.lastPeerExchange = req.body;
      const uri = req.body.uri || '';
      const parts = uri.replace('pyana://', '').split('/');
      res.json({
        ref_id: `ref_${Date.now()}`,
        cell_id: parts[1] || 'unknown',
        node_id: parts[0] || 'unknown',
        permissions: 'read,write',
      });
    });

    // Registry: mount a service.
    this.app.post('/registry/mount', (req, res) => {
      this.state.lastMountRequest = req.body;
      const entry = {
        name: req.body.path?.split('/').pop() || 'unnamed',
        path: req.body.path,
        kind: req.body.kind || 'service',
        version: 1,
        tags: req.body.tags || [],
      };
      this.state.services.push(entry);
      res.json({ path: entry.path, version: entry.version, kind: entry.kind });
    });

    // Registry: discover services by tag.
    this.app.get('/registry/discover', (req, res) => {
      const tags = (req.query.tags as string || '').split(',').filter(Boolean);
      let results = this.state.services;
      if (tags.length > 0) {
        results = results.filter(s => tags.some(t => s.tags.includes(t)));
      }
      res.json({ results });
    });

    // Registry: resolve path.
    this.app.get('/registry/resolve/*', (req, res) => {
      const path = '/' + (req.params[0] || '');
      if (path === '/') {
        res.json({ entries: this.state.services });
        return;
      }
      const match = this.state.services.find(s => s.path === path);
      if (match) {
        res.json({ ...match, sturdyRef: `pyana://node_mock_001/${match.name}` });
      } else {
        res.status(404).json({ error: 'Path not found' });
      }
    });

    // Storage: write file.
    this.app.post('/files/write', (req, res) => {
      const data = req.body.data || '';
      const hash = `sha256_${Buffer.from(data).toString('hex').slice(0, 16)}`;
      this.state.storedFiles.set(hash, data);
      this.state.quota.bytesStored += data.length;
      this.state.quota.objectCount += 1;
      res.json({ hash, size: data.length });
    });

    // Storage: read file by hash.
    this.app.get('/files/read/:hash', (req, res) => {
      const content = this.state.storedFiles.get(req.params.hash);
      if (content) {
        res.json({ hash: req.params.hash, data: content, size: content.length });
      } else {
        res.status(404).json({ error: 'Content not found' });
      }
    });

    // Storage: quota.
    this.app.get('/storage/quota', (_req, res) => {
      res.json(this.state.quota);
    });

    // Intents: fulfill.
    this.app.post('/intents/fulfill', (req, res) => {
      res.json({
        fulfilled: true,
        intent_id: req.body.intent_id,
        receipt: 'mock_fulfill_receipt',
      });
    });
  }

  async start(): Promise<void> {
    return new Promise((resolve) => {
      this.server = this.app.listen(this.port, () => {
        resolve();
      });
    });
  }

  async stop(): Promise<void> {
    return new Promise((resolve) => {
      if (this.server) {
        this.server.close(() => resolve());
      } else {
        resolve();
      }
    });
  }

  reset(): void {
    this.state = this.defaultState();
  }

  get url(): string {
    return `http://localhost:${this.port}`;
  }
}
