# Agda from Nothing

A workshop on learning Agda with minimal prerequisites.

### Installing Agda

#### Docker with Emacs and exercises
I created a Docker image with Agda, Emacs and the exercises. See [scottfleischman/agda-from-nothing](https://hub.docker.com/r/scottfleischman/agda-from-nothing/)

#### Official Agda installation instructions
* http://agda.readthedocs.io/en/latest/getting-started/installation.html
* http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download

#### On Mac
You may find `stack` more reliable than `cabal` to build Agda.

1. Install [stack](http://docs.haskellstack.org/en/stable/install_and_upgrade/#mac-os-x)
2. In a terminal run: `stack install --resolver nightly-2016-05-08 Agda`
3. Install [Aquamacs](http://aquamacs.org/)
4. In a terminal run: `agda-mode setup`
5. (Restart Aquamacs)

#### Docker with Agda only
See [banacorn/docker-agda](https://github.com/banacorn/docker-agda).
