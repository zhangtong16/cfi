# Type-based Control Flow Integrity

This is a Type-based Control Flow Integrity enforcement implementation build on top of LLVM compiler infrastructure.

Currently, there are two phases:

1. __Type Analysis for ICalls__. We currently use `FLTA`, which means First Layer Type Analysis, to analyze the type of icalls, and resolve the candidate targets set.
2. __Instrumentation for Runtime Check__. Before every icalls, we insert checks to determine the target is in the candidate sets.

## Features

- [x] FLTA
- [ ] MLTA
- [ ] Shadow Stack
- [ ] Protection of Metadata
- [x] Runtime Check
