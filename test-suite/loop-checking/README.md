# Plugin to run universe checking using Bezem & Coquand's loop-checking algorithm

This is directly based on the plugin-demo, see that plugin for documentation on how to use 
the extractable template monad.

# Universe checking

The plugin adds a new command:

`MetaCoq Check Universes`

This can be used at any point in a file to launch a check that the universe constraints declared
at this point do not imply a loop and hence have a model in natural numbers. The model is printed 
as output (along with timing information if `MetaCoq Set Timing` is set).

The `theories/test.v` file performs this check on all files in the Coq Standard Library.