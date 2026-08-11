# Editor support

Syntax highlighting for `.sn` / `.sni`, plus a client for the interpreter's own
language server (`snel lsp` — always available, in both the Rust and C builds).

## vim

Copy the trees into your runtime path, e.g.:

    cp -r editors/vim/* ~/.vim/

Provides syntax highlighting, `--` comments, and 2-space indentation.

## emacs

    (add-to-list 'load-path "/path/to/snel/editors/emacs")
    (require 'snel-mode)

Provides font-locking, comments, bracket-depth indentation, and — with
[eglot](https://github.com/joaotavora/eglot) — registers `snel lsp` as the
language server for `snel-mode`.

## vscode

Syntax highlighting works with no dependencies. The LSP client needs
`vscode-languageclient`, so it is one `npm install` away.

    cargo build --release            # the server is the interpreter itself
    cd editors/vscode && npm install

Then either press **F5** (Run Extension — opens a second window with the
extension loaded), or install it for real and reload:

    npx @vscode/vsce package --allow-missing-repository -o /tmp/snel.vsix
    code --install-extension /tmp/snel.vsix --force

Open any `.sn` file: errors show up as squiggles, and the server's log is under
Output → "snel".

`snel.serverPath` says where the interpreter is (default `snel`, found on
PATH). It expands `${workspaceFolder}`, so a checkout-local build works:

    { "snel.serverPath": "${workspaceFolder}/target/release/snel" }

`snel.enableServer: false` turns the client off and leaves highlighting alone.
