This is the same as SDPL version 2 except that we move to using director strings to track free variables.  The use of director 
strings is crude and unpolished, but it speeds some operations up considerably.

Version 4 will do collets i.e. co-llets i.e. co-linear-lets

Version 5 will interleave collets into symbolic differentiation 
to give even more speedups.


To compile with all optimizations on, use 

ghc --make -O2 -pgmlo $LLCOPT -pgmlc $LLCCOMP -fllvm (+other optimizations, +llvm specific optimizations)

- $LLCOPT 
should be something like opt or opt-6.0 if you're running ubuntu
- $LLCOMP 
should be something like llc or llc-6.0 if you're running ubuntu

if you want to pass specific options to llvm compiler (llc) use -optlc $OPTION
if you want to pass specific options to llvm optimizer (opt) use -optlo $OPTION

For example 

ghc --make -O2 -pgmlo opt-6.0 -pgmlc llc-6.0 -fllvm -fspecialize-aggressively -fstatic-argument-transformation -funbox-strict-fields -fworker-wrapper -fsimplifier-phases=8 Main.hs

On arch linux (with llvm9):

ghc -dynamic --make -O2 -pgmlo opt -pgmlc llc -fllvm -fspecialize-aggressively -fstatic-argument-transformation -funbox-strict-fields -fworker-wrapper -fsimplifier-phases=8 Main.hs

On arch linux (without llvm9):
ghc -dynamic --make -O2  -fspecialize-aggressively -fstatic-argument-transformation -funbox-strict-fields -fworker-wrapper -fsimplifier-phases=8 Main.hs

The static argument transformation is a neat one.  A lot of recursive functions 
pass in arguments that aren't always used, and they're just passed down the chain of command
until needed.  In this case the argument can be lifted and a localized loop can be run 
that gets those arguments to the appropriate nodes.
