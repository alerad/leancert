# Python Trust Boundary

Python is responsible for modeling, orchestration, candidate search, and
presentation. It is not allowed to declare its own heuristic candidate a
proof.

```text
exact Python claim
        │
        ▼
normalization + semantic digest
        │
        ▼
untrusted candidate search ──► candidate bound / cutoff / Krawczyk data
                                      │
                                      ▼
                           negotiated LeanCert checker
                                      │
                         accepted fixed certificate
                                      │
                  ┌───────────────────┴───────────────────┐
                  ▼                                       ▼
       typed Python outcome                    exported Lean project
                                                          │
                                                          ▼
                                             independent kernel rebuild
```

## What `Verified` means

A v1 `Verified` result means:

- the request was a closed, normalized exact claim;
- the Bridge advertised the operation and schema used;
- the response matched the negotiated backend, certificate schema, and
  verification route;
- the certificate payload agreed with the original request; and
- the named checked operation accepted it.

It does not mean every Python module, search heuristic, NumPy operation, or
compiler optimization has joined the trusted computing base.

## Compiled checking and kernel replay are separate events

The bundled Bridge reports a `compiled_checker` verification route. Exporting
and rebuilding a fixed certificate is a second event: the generated project
kernel-reduces the retained checker input, applies the soundness theorem, and
uses `#assert_trust kernel` on the resulting theorem.

Do not relabel the original Bridge result as a kernel-replay result. Record both
events when an audit requires both.

## Provenance

Verified outcomes retain:

- Python claim digest and normalized claim;
- Bridge API and protocol versions;
- Lean and LeanCert versions;
- source revision and source digest;
- build-environment digest and profile;
- resolved Lean toolchain and LeanCert dependency revision; and
- the negotiated capability identity.

Run `leancert doctor --json` to inspect the installed runtime independently of
a particular proof.
