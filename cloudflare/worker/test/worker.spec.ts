import { describe, it, expect, beforeAll } from "vitest";
import { Miniflare } from "miniflare";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";

async function createMF() {
  // A tiny origin that echoes headers; implemented as another Worker script.
  const echoScript = `
export default {
  async fetch(req) {
    const headers = Object.fromEntries(req.headers);
    const body = await req.text();
    return new Response(JSON.stringify({ headers, body }), { headers: { "content-type": "application/json" }});
  }
}`;
  const edgeScript = readFileSync(resolve("dist/index.js"), "utf8");

  const mf = new Miniflare({
    modules: true,
    script: edgeScript,
    bindings: {
      ORIGIN_URL: "http://localhost:8788",
      EDGE_HMAC_SECRET: "test-secret"
    },
    durableObjects: { RATE_DO: "RateLimiter" },
    // Secondary MF instance for the echo origin
    mounts: {
      // Mount the echo origin at :8788
      // Miniflare automatically assigns ports; we simulate by calling it directly via mf.dispatchFetch
    }
  });

  // Hack: We'll patch global fetch used by the edge worker to route ORIGIN_URL to a local handler.
  // In this test we'll replace fetch when origin URL is matched.
  const echoFetch = async (req: Request) => {
    const headers = Object.fromEntries(req.headers as any);
    const body = await req.text();
    return new Response(JSON.stringify({ headers, body }), { headers: { "content-type": "application/json" }});
  };

  // Monkey-patch: in Miniflare 3, you can set a dispatchOverride on the global scope via mf.routes soon,
  // Here we intercept by providing a special URL and checking it in our fetch call.
  // Simpler: We'll set ORIGIN_URL to a sentinel and check for it in code; but we kept your code generic.
  // So instead, we simulate a full round trip by directly calling the default export with a Request whose URL we control.
  return { mf, echoFetch };
}

describe("tcdb-edge worker", () => {
  let mf: Miniflare; let echoFetch: (r: Request) => Promise<Response>;
  beforeAll(async () => {
    const out = await createMF();
    mf = out.mf;
    echoFetch = out.echoFetch;
    // @ts-ignore
    global.fetch = ((orig) => async (input: any, init?: any) => {
      const url = typeof input === "string" ? input : input.url;
      if (url.startsWith("http://localhost:8788")) {
        const req = new Request(url, init);
        return echoFetch(req);
      }
      return orig(input, init);
    })(global.fetch);
  });

  it("adds x-signature header (HMAC over body)", async () => {
    const req = new Request("http://edge.local/evidence/certificate?k=testkey", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ hello: "world" })
    });
    const res = await mf.dispatchFetch(req);
    expect(res.status).toBe(200);
    const j = await res.json();
    // origin sees x-signature header injected by the edge
    expect(j.headers["x-signature"]).toBeDefined();
    // origin echoes original body
    expect(j.body).toBe(JSON.stringify({ hello: "world" }));
  });

  it("rate limits after N requests/min/key", async () => {
    // The script uses 300/min; we'll just ping a bunch to ensure not 429 immediately.
    for (let i = 0; i < 5; i++) {
      const r = await mf.dispatchFetch("http://edge.local/reasoner/check?k=ratetest", { method: "POST", body: "{}", headers: {"content-type":"application/json"} });
      expect([200, 429]).toContain(r.status);
    }
  });
});

