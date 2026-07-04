#!/usr/bin/env python3
# The IO shell: a socket reactor driving the proven sans-IO orb core.
# NOT verified — this is the untrusted environment boundary (per the assurance
# principle: the socket/kernel is tested, our core is proven). One subprocess
# per request: deliberately simple and slow. The request PROCESSING is the Lean
# `orb` binary, whose parse+resolve path is theorem-backed.
import socketserver, subprocess, sys, os
ORB = os.environ.get("ORB",
    os.path.join(os.path.dirname(__file__), "..", ".lake", "build", "bin", "orb"))
class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        data = self.request.recv(65536)
        out = subprocess.run([ORB], input=data, capture_output=True).stdout
        self.request.sendall(out)
if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8080
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer(("127.0.0.1", port), Handler) as srv:
        print(f"orb reactor on 127.0.0.1:{port} -> {ORB}", flush=True)
        srv.serve_forever()
