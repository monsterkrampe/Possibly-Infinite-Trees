# Possibly Infinite Trees

This repo formalizes (possibly) infinite trees of finite degree in Lean.
So far this is mainly a dependency for [one of my other projects](https://github.com/monsterkrampe/Existential-Rules-in-Lean) and tailored towards this porpose. 
The repo features a formalization of (a special case of) König's Lemma. 

Do not hesitate to reach out if you think that this can be useful for you but current specifics of the implementation/formalization do not quite work out!

## Notes on Setup

Using [`elan`](https://github.com/leanprover/elan) / `lake`:

- Install `elan`, e.g. via `nix-shell -p elan` or simply `nix develop` if you are using nix.
- Run `lake build` to build the project. If the build is successful, the proofs are correct :tada:

