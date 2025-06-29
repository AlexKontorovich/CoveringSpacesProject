# Covering Spaces Project
Organized by Alex Kontorovich and John Morgan

## Zulip

The project will be coordinated via a [Lean Zulip channel](https://leanprover.zulipchat.com).

## Blueprint

This project has a blueprint, which is available at <https://AlexKontorovich.github.io/CoveringSpacesProject/web/>.

To use the tool, first install local requirements using
```sh
pip install -r blueprint/requirements.txt
```

Then compile documentations using `make blueprint` in the top-level directory. Alternatively, if the PDF is needed, type
```sh
cd blueprint
make pdf
```

## Use of LaTeX inside Lean

For those using github's copilot (free for educators), it's very convenient to have the natural language statements
right next to the Lean to be formalized. So we write the blueprint TeX right in the *.lean document, separated by
delimiters `/-%% text here %%-/` for multi-line and `--%% text here` for single-line TeX. The code automatically
scrapes these and populates the blueprint accordingly.


## Quick contributions via gitpod
If you want to quickly contribute to the project without installing your own copy of lean, you can do so using gitpod.
Simply visit: <https://gitpod.io/new/#https://github.com/AlexKontorovich/CoveringSpacesProject/>, or click the button below:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/new/#https://github.com/AlexKontorovich/CoveringSpacesProject/)

All the required dependencies will be loaded (this takes a few minutes), after which you will be brought to a web-based
vscode window, where you can edit the code, and submit PR's.
