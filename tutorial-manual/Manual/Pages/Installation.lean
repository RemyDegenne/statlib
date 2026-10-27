import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation and Setup" =>
%%%
htmlSplit := .never
%%%

This tutorial guides you through installing Lean and setting up Statlib.

# Installing Lean

Before using Statlib, install Lean 4 and Lake by following the official
instructions at [lean-lang.org/install](https://lean-lang.org/install/).

# Installing Statlib

The Statlib source is available at
[github.com/stat-lib/statlib](https://github.com/stat-lib/statlib).

Clone the repository and create a working branch:

```
git clone https://github.com/stat-lib/statlib.git
cd statlib
git checkout -b my-statlib-branch
```

Build the Lean library:

```
lake exe cache get
lake build
```

You can then import Statlib from Lean files:

```
import Statlib
import Statlib.Inference.Inference
```
