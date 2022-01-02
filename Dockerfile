FROM archlinux

# Install system-wide dependencies (there are a lot of them! almost 4
# gigs, most of which comes from texlive)
RUN pacman --noconfirm -Syu
RUN pacman --noconfirm -Syu base-devel sassc
RUN pacman --noconfirm -Syu npm
RUN pacman --noconfirm -Syu texlive-core texlive-pictures texlive-latexextra rubber
RUN pacman --noconfirm -Syu git
RUN pacman --noconfirm -Syu rsync

RUN useradd -ms /bin/bash build
USER build
WORKDIR /home/build

RUN \
  git clone https://aur.archlinux.org/pandoc-bin.git; \
  cd pandoc-bin; \
  makepkg;

RUN \
  git clone https://aur.archlinux.org/stack-static.git; \
  cd stack-static; \
  makepkg --skipinteg;

USER root
RUN \
  pacman --noconfirm -U pandoc-bin/*.pkg.tar.zst \
    stack-static/*.pkg.tar.zst; \
  rm -fr pandoc-bin stack-static

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
  stack install -j4 --ghc-options "-j12" shake; \
  stack install -j4 --ghc-options "-j12" pandoc-types; \
  stack install -j4 --ghc-options "-j12" tagsoup; \
  stack install -j4 --ghc-options "-j12" unordered-containers; \
  stack install -j4 --ghc-options "-j12" uri-encode; \
  stack install -j4 --ghc-options "-j12" Agda; \
\
  git clone https://git.amelia.how/amelia/agda-reference-filter.git; \
  cd agda-reference-filter; \
  stack config set resolver lts-18.18; \
  stack install; \
\
  cd ..; \
  rm -rf agda-reference-filter; \
  git clone https://git.amelia.how/amelia/agda-fold-equations.git; \
  cd agda-fold-equations; \
  stack config set resolver lts-18.18; \
  stack install; \
\
  cd ..; \
  rm -rf agda-fold-equations; \
  stack exec -- ghc Shakefile.hs -o /root/.local/bin/1lab-shake; \
\
  mv $(/root/.local/bin/agda --print-agda-dir) /root/Agda -v; \
  rm -rf /root/.stack

RUN \
  mkdir -p $(dirname $(/root/.local/bin/agda --print-agda-dir)); \
  ln -sf /root/Agda/ $(/root/.local/bin/agda --print-agda-dir);

# Fetch fonts
RUN \
  mkdir -p /root/static/{ttf,woff2,otf}; \
  curl -L https://cubical.1lab.dev/static/woff2/iosevk-abbie-regular.woff2    -o /root/static/woff2/iosevk-abbie-regular.woff2; \
  curl -L https://cubical.1lab.dev/static/ttf/iosevk-abbie-regular.ttf        -o /root/static/ttf/iosevk-abbie-regular.ttf; \
  curl -L https://cubical.1lab.dev/static/otf/texgyrepagella-regular.otf      -o /root/static/otf/texgyrepagella-regular.otf; \
  curl -L https://cubical.1lab.dev/static/otf/texgyrepagella-bold.otf         -o /root/static/otf/texgyrepagella-bold.otf; \
  curl -L https://cubical.1lab.dev/static/otf/texgyrepagella-italic.otf       -o /root/static/otf/texgyrepagella-italic.otf; \
  curl -L https://cubical.1lab.dev/static/otf/texgyrepagella-bolditalic.otf   -o /root/static/otf/texgyrepagella-bolditalic.otf;

WORKDIR /workspace
