# Choose Python or Lean

LeanCert exposes the same checked numerical foundations through two workflows.
Choose the interface that matches where your theorem starts.

| Choose Python when... | Choose Lean when... |
|---|---|
| Your model, data, or search procedure already lives in Python | Your proposition is already a Lean theorem |
| You want a self-contained `pip install` experience | You want tactics inside an existing Lean development |
| NumPy or PyTorch supplies untrusted candidate data | You want direct access to LeanCert certificate APIs |
| You want typed `Verified`/`Rejected`/`Inconclusive` outcomes | You want a theorem immediately available to downstream Lean code |
| You want to export a fixed certificate for later audit | You want to construct or compose certificates manually |

The choice is not a choice of mathematical authority. In the Python workflow,
candidate discovery remains untrusted and the bundled Bridge invokes LeanCert's
checked operations. Replayable result families can then be exported as pinned
Lean projects and rebuilt with the Lean kernel.

## Begin with Python

```bash
pip install leancert
leancert doctor
```

Continue to the [Python quickstart](python/quickstart.md).

## Begin with Lean

Add LeanCert to a Lake project and continue to the
[Lean quickstart](quickstart.md).

## Use both

A common workflow is:

1. Describe an exact claim in Python.
2. Let Python search for candidate numerical data.
3. Accept success only after a LeanCert checker validates that data.
4. Export the retained certificate.
5. Rebuild the exported theorem independently and import the mathematical idea
   into a larger Lean development.
