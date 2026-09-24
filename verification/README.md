# Comparator

[Comparator](https://github.com/leanprover/comparator) rechecks the theorem in
[Triangle.lean](../Triangle.lean) and its dependencies, including Mathlib lemmas,
through Lean's kernel. It permits only `propext`, `Quot.sound` and
`Classical.choice`.

On Linux with systemd, install [Landrun](https://github.com/Zouuup/landrun)
(requires Go 1.24 or later):

```sh
GOBIN="$HOME/.local/bin" go install \
  github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
export PATH="$HOME/.local/bin:$PATH"
```

From the repository root:

```sh
cd verification
lake exe cache get
lake build comparator lean4export
systemd-run --user --wait --pipe --collect \
  -p RestrictAddressFamilies=~AF_UNIX -E PATH --working-directory="$PWD" \
  -- lake env comparator comparator.json
```

Success ends with
`Lean default kernel accepts the solution` and `Your solution is okay!`.
