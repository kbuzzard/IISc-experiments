# IISc-experiments

Some material for Lean 4 lectures at IISc.

Written in Bengaluru, April 2023.

## Learning resources (how do I learn?)

See the [RESOURCES](RESOURCES.md) file.

## How to run this repo yourself?

### Local installation

This is the best way; you can edit files and experiment, and you won't lose them.
It's also the hardest way: it involves typing stuff in on the command line. 

In brief: first install Lean 4 following the instructions [here](https://leanprover.github.io/lean4/doc/quickstart.html).

Then download and install this project by going to its [home page on GitHub](https://github.com/kbuzzard/IISc-experiments),
clicking "Code" and "local", and then downloading the project onto your computer.

Pic: ![local installation](png/codelocal.png?raw=true "local installation")

Next open a command line in the project folder, type `lake exe cache get`, and wait until all files are downloaded and installed and your cursor has reappeared.

Finally, open the root directory of the project folder in VS Code. You can open the files in the `IIScExperiments` directory (not the `IIScExperiments.lean` Lean file!) and these correspond to the material I was going through in lectures.

### Remote running via GitPod

You don't need to install anything onto your computer using this method.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/kbuzzard/IISc-experiments)

Note to self: I got gitpod working by adding the files `.gitpod.yml` and `.docker/gitpod/Dockerfile`

### Remote running via Codespaces

You don't need to install anything onto your computer using this method.

Go to the project's [home page on GitHub](https://github.com/kbuzzard/IISc-experiments),
click "Code" and then "Codespaces" so it looks like this:

Pic: ![codespaces installation](png/codespaces.png?raw=true "codespaces installation")

Then click "create codespace on main", and then wait for a few minutes. When it looks like everything has downloaded, open up the `IIScExperiments` directory (not the file!) and the code I've been using in the lectures should just work.

Note to self: I got codespaces working by adding the files `.devcontainer/devcontainer.json` and `.devcontainer/Dockerfile`.
