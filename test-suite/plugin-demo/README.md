# Writing a Plugin with the Extractable Monad

You can use `Template.TemplateMonad.Extractable` to write plugins in Gallina.
You can use this project as a template for doing this.

## How to use it

1. Write your plugin inside the `theories` directory. The plugin should use
   the `Template.TemplateMonad.Extractable` monad to interact with Rocq.
2. Modify `src/ExtractDemo.v` to extract the modules that you want to call
   from your plugin, and list them in the `extracted_modules` field of the
   `rocq.extraction` stanza of `src/dune`. Do not list the modules that the
   extractable template-rocq plugin already provides: they are shared with
   `-open Metarocq_template_plugin`, see `src/template-extractable/dune`.
3. In the `src` directory, write the entry point to your plugin. See
   `src/g_demo_plugin.mlg` for some examples. Its `DECLARE PLUGIN` name must
   be the findlib name of the plugin library (its `public_name`).
4. Load the plugin with `Declare ML Module` in a file of `theories`
   (see `theories/Loader.v`), and list the plugin in the `plugins` field of
   the `rocq.theory` stanza.
5. Run `dune build` and you should be good to go.

## How it works

The `rocq.extraction` stanza of `src/dune` compiles `src/ExtractDemo.v`,
which extracts the Gallina code of the plugin to OCaml in `src`. The plugin
library then links the extracted modules with the entry point of the plugin,
on top of the extractable template-rocq plugin, which provides the OCaml
code for the modules that are shared by all extracted plugins and the
quoting and unquoting functions.
