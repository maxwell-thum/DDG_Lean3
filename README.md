# DDG_Lean3
Formalizing Discrete Differential Geometry in Lean 3. Details will be found on the [project website](https://maxwell-thum.github.io/DDG_Lean3/).

Much of the project infrastructure has been adapted from the [unit fractions project](https://github.com/b-mehta/unit-fractions), the [sphere eversion project](https://leanprover-community.github.io/sphere-eversion/), and the [liquid tensor experiment](https://leanprover-community.github.io/lean-liquid/).

# Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To obtain this repo, run `leanproject get https://github.com/maxwell-thum/DDG_Lean3`. If you already have the repo, you can
update it with `git pull` followed by `leanproject get-mathlib-cache`.

To build the repo, run `leanproject build`.

# Build the blueprint

To build the web version of the blue print, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip3 install invoke pandoc
cd .. # go to folder where you are happy clone git repos
git clone git@github.com:plastex/plastex
pip3 install ./plastex
git clone git@github.com:PatrickMassot/leanblueprint
pip3 install ./leanblueprint
cd DDG_Lean3
```

To actually build the blueprint, run
```
leanproject get-mathlib-cache
leanproject build
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.
