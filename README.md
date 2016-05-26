# Agda from Nothing

A workshop on learning Agda with minimal prerequisites.

### Installing Agda
The exercises are written for Agda 2.5.1.

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

#### Docker

##### Docker with Emacs and exercises
I created a Docker image with Agda, Emacs and the exercises. See [scottfleischman/agda-from-nothing](https://hub.docker.com/r/scottfleischman/agda-from-nothing/)

`docker run -it scottfleischman/agda-from-nothing`

**Note** The Mac Terminal has issues sending common control sequences such as Control+Comma. It may be better to do a full install as above, or use Docker with Agda as below with a local editor and agda-mode.

##### Docker with Agda only
See [banacorn/docker-agda](https://github.com/banacorn/docker-agda).

### Emacs Keybindings
See the [Agda docs](http://agda.readthedocs.io/en/latest/tools/emacs-mode.html) for all of the keybindsings. Here are ones I commonly use. Note `C-` means `Control+`.

#### Global (can be used anywhere)
* C-c C-l — Load file. I use this constantly.
* C-c C-f	— Move to next goal (**f**orward)
* C-c C-b — Move to previous goal (**b**ackwards)
* C-c C-d — Infer (**d**educe) type. Type in any expression and it infers the type.
* C-c C-n — Compute **n**ormal form. In other words, reduces the expression as much as possible.
* C-g — Quit what command sequence you started.

#### In a hole/goal
* C-c C-c — Case split. Type in an argument name and it creates lines for each possible case. It works with multiple arguments.
* C-u C-c C-Comma — Show unnormalized goal type and context.
* C-u C-u C-c C-Comma — Show fully normalized goal type and context.
* C-c C-Space — Give (fill goal). Type checks the expression you typed in the hole, and if successful fills the hole.
* C-c C-r — Refine. Partial give: makes new holes for missing arguments.
  * If you've entered an expression in the hole, it will fill in the hole with that expression and make new holes for any missing arguments.
  * If you haven't entered anything in the hole, and if the hole is constrained to one constructor, it fills in the hole with that constructor and makes new holes for each of the constructor's arguments.
* C-c C-a — Automatic Proof Search (Auto). Tries to fill the hole with any solution. Note—this may not be a correct solution if the types aren't precise enough to constrain the term to only correct ones. Note also that it often fails to find a solution.

#### Unicode characters
* `\r-` or `\to` for `→`
* `\==` for `≡`
* `\==n` for `≢`
* `\all` for `∀`
* `\<=` for `≤`
* `\<=n` for `≰`
* `\ell` for `ℓ`
* `\lambda` or `\Gl` for `λ`
* `\'` for `′`
* `\::` for `∷` (it looks like two colons, but it is a single Unicode character)
* `\_0` for `₀` (subscript 0)
* `\_1` for `₁` (and so on)
* `\^0` for `⁰` (superscript 0)
* `\^1` for `¹` (and so on)
* `\in` for `∈`
* `\ni` for `∋`
* `\lub` for `⊔` (least upper bound; max)
* `\Pi` for `Π`
* `\Sigma` or `\GS` for `Σ`
* To see info on a character under the cursor, use `C-u C-x Equals`
