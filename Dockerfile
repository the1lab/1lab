FROM archlinux

# Install system-wide dependencies (there are a lot of them! almost 4
# gigs, most of which comes from texlive)
RUN pacman --noconfirm -Syu
RUN pacman --noconfirm -S base-devel sassc
RUN pacman --noconfirm -S npm
RUN pacman --noconfirm -S texlive-core texlive-pictures texlive-latexextra rubber
RUN pacman --noconfirm -S git

RUN useradd -ms /bin/bash build
USER build
WORKDIR /home/build

RUN \
  git clone https://aur.archlinux.org/pandoc-bin.git; \
  cd pandoc-bin; \
  makepkg;

RUN \
  git clone https://aur.archlinux.org/agda-bin-git.git; \
  cd agda-bin-git; \
  makepkg;

RUN \
  git clone https://aur.archlinux.org/stack-static.git; \
  cd stack-static; \
  makepkg --skipinteg;

USER root
RUN \
  pacman --noconfirm -U pandoc-bin/*.pkg.tar.zst \
    agda-bin-git/*.pkg.tar.zst \
    stack-static/*.pkg.tar.zst

WORKDIR /root/

# Needed for building equations
RUN npm i -g katex

# Add stack executables (agda-fold-equations, agda-reference-filter) and
# npm executables (mostly KaTeX) to the path
RUN echo "export PATH=\$PATH:\$HOME/.local/bin" >> /root/.bashrc

ADD Shakefile.hs /root/Shakefile.hs

# Install Haskell dependencies - this contributes another ~3 or so gigs
# to the image size. Unfortunately the Arch Haskell packages are
# irreparably broken. This is a time-space tradeoff: we use a lot more
# space duplicating these, to save the time spent building Pandoc and
# Agda. (pandoc-types is only ~7 Haskell modules)
RUN \
  mkdir -p /root/.stack/global-project/; \
  echo -e "packages: []\nresolver: lts-18.18" >> /root/.stack/global-project/stack.yaml

RUN \
  stack install -j16 shake; \
  stack install -j16 pandoc-types; \
  stack install -j16 tagsoup; \
  stack install -j16 unordered-containers; \
  stack install -j16 uri-encode; \
  git clone https://git.amelia.how/amelia/agda-reference-filter.git; \
  cd agda-reference-filter; \
  stack config set resolver lts-18.18; \
  stack install; \
  cd ..; \
  rm -rf agda-reference-filter; \
  git clone https://git.amelia.how/amelia/agda-fold-equations.git; \
  cd agda-fold-equations; \
  stack config set resolver lts-18.18; \
  stack install; \
  cd ..; \
  rm -rf agda-fold-equations; \
  stack exec -- ghc Shakefile.hs -o /root/.local/bin/1lab-shake; \
  rm -rf /root/.stack

RUN \
  mkdir -p $(dirname $(agda --print-agda-dir)); \
  ln -sf /usr/share/agda/ $(agda --print-agda-dir);

WORKDIR /workspace
