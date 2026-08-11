// Minimal LSP client: launches `snel lsp` over stdio for diagnostics and hover.
// Syntax highlighting is declarative and needs none of this; everything below is
// about the server. When it cannot start, say so in the "Snel" output channel
// (and, for the cases a user can fix, in a notification) rather than failing
// silently — a quiet no-op here is indistinguishable from "the LSP is broken".
const { workspace, window, commands } = require("vscode");
const fs = require("fs");
const path = require("path");

let client;
let log;

// `snel.serverPath` may name a binary on PATH, or a path inside the workspace
// written with `${workspaceFolder}` — VS Code does not expand that itself for
// an arbitrary setting, so do it here.
function resolveServerPath(configured) {
  const folder = workspace.workspaceFolders && workspace.workspaceFolders[0];
  const root = folder ? folder.uri.fsPath : "";
  const p = configured.replace(/\$\{workspaceFolder\}/g, root);
  return path.isAbsolute(p) || p.includes(path.sep) ? path.resolve(root, p) : p;
}

async function start() {
  await stop();
  const cfg = workspace.getConfiguration("snel");
  if (!cfg.get("enableServer", true)) {
    log.appendLine("snel.enableServer is false — not starting the server.");
    return;
  }

  let LanguageClient, TransportKind;
  try {
    ({ LanguageClient, TransportKind } = require("vscode-languageclient/node"));
  } catch (e) {
    const msg =
      "Snel: vscode-languageclient is missing, so there are no diagnostics " +
      "(syntax highlighting still works). Run `npm install` in editors/vscode " +
      "and repackage the extension.";
    log.appendLine(msg + "\n" + e);
    window.showWarningMessage(msg);
    return;
  }

  const command = resolveServerPath(cfg.get("serverPath", "snel"));
  // A bare name is left to PATH; an explicit path that is missing is worth
  // saying out loud, or the server just fails to start with nothing to read.
  if (command.includes(path.sep) && !fs.existsSync(command)) {
    const msg =
      `Snel: no interpreter at ${command}. Build it (\`cargo build --release\`) ` +
      "or set `snel.serverPath`. Syntax highlighting still works.";
    log.appendLine(msg);
    window.showWarningMessage(msg);
    return;
  }

  log.appendLine(`starting: ${command} lsp`);
  const serverOptions = {
    run: { command, args: ["lsp"], transport: TransportKind.stdio },
    debug: { command, args: ["lsp"], transport: TransportKind.stdio },
  };
  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "snel" }],
    outputChannel: log,
  };
  client = new LanguageClient("snel", "Snel language server", serverOptions, clientOptions);
  await client.start();
  log.appendLine("server started");
}

async function stop() {
  if (client) {
    const c = client;
    client = undefined;
    await c.stop();
  }
}

function activate(context) {
  log = window.createOutputChannel("Snel");
  context.subscriptions.push(log, { dispose: stop });
  context.subscriptions.push(
    commands.registerCommand("snel.restartServer", () => start()),
    workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("snel")) start();
    })
  );
  start();
}

function deactivate() {
  return stop();
}

module.exports = { activate, deactivate };
