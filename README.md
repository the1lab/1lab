# [Cubical 1lab](https://cubical.1lab.dev)

A section of the 1lab dedicated to mathematics done in Homotopy Type
Theory. We have a Discord server for asking questions/discussing
contributions/yelling at Amy for being bad at explaining things: [join
here!]

[join here]: https://discord.gg/NvXkUVYcxV

## Building

The recommended way of building the 1Lab is using Docker. The Dockerfile
in the repository builds an Arch Linux installation with everything
needed to build, and the build script precompiled as `1lab-shake`. The
image is also on docker.io, so you can ruin it like this:

```
% docker run -it -v $PWD:/workspace docker.io/pltamy/1lab:latest /bin/bash -i
$ 1lab-shake all -j # (in the container)
```

A complete deployment also redistributes parts of the following free
software projects:

* KaTeX CSS & fonts: put `katex.min.css` under `_build/html/css/`, and
the KaTeX font files under `_build/html/css/fonts`.

* Iosevka (as iosevk-abbie): Either build it yourself or get mine
[here](https://files.amelia.how/3OYp.xz), as a xz'd tar. Put the `woff2`
and `ttf` directories of the tar under static/.
