# 1lab-shake & agda-typed-html

Haskell commands used for building the 1Lab.

**1lab-shake**: Our Shakefile. (main-is: `Main.hs`)

**agda-typed-html**: Wrapper around Agda which builds HTML output with
type information on every link. (main-is: `Wrapper.hs`).

## Install

Use nix:

```
nix-env -if https://github.com/plt-amy/1lab/archive/refs/heads/main.tar.gz -A agda-typed-html
```
