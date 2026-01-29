import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { ProofState } from "../../../types";
import vscodeRequest from "../../../services/vscodeRequest";
import fetchViaExternalProcess from "./fetchViaExternalProcess";

/**
 * Checks if an error indicates that the RPC method is not found.
 * This happens when the user hasn't added `import Paperproof` to their file.
 */
const isMethodNotFoundError = (error: any): boolean => {
  const message = error?.message || String(error);
  // Lean returns "unknown method" or "method not found" for missing RPC methods
  return message.includes("unknown method") ||
         message.includes("method not found") ||
         message.includes("Paperproof.getSnapshotData");
};

/**
 * Converts a VS Code URI to a file system path.
 */
const uriToPath = (uri: string): string => {
  return vscode.Uri.parse(uri).fsPath;
};

/**
 * Fetches proof data via RPC (fast path) or CLI fallback (when import Paperproof is missing).
 */
const fetchLeanData = async (log: vscode.OutputChannel, client: any, tdp: TextDocumentPositionParams): Promise<ProofState> => {
  const uri = tdp.textDocument.uri;
  const config = vscode.workspace.getConfiguration('paperproof');
  const mode = config.get('isSingleTacticMode') ? 'single_tactic' : 'tree';

  // Try RPC first (fast path - works when import Paperproof is present)
  try {
    if (mode === 'single_tactic') {
      const proofTreeResponse = await vscodeRequest(log, "Paperproof.getSnapshotData", client, uri, tdp, { pos: tdp.position, mode });
      return {
        goal: null,
        proofTree: proofTreeResponse.steps,
        version: proofTreeResponse.version ?? undefined
      };
    } else {
      const proofTreeResponse = await vscodeRequest(log, "Paperproof.getSnapshotData", client, uri, tdp, { pos: tdp.position, mode });
      const goalsResponse = await vscodeRequest(log, "Lean.Widget.getInteractiveGoals", client, uri, tdp, tdp);
      return {
        goal: (goalsResponse && goalsResponse.goals[0]) || null,
        proofTree: proofTreeResponse.steps,
        version: proofTreeResponse.version ?? undefined
      };
    }
  } catch (error) {
    // If the RPC method is not found, fall back to CLI
    if (isMethodNotFoundError(error)) {
      log.appendLine("RPC method not found, falling back to CLI...");
      return fetchViaCliFallback(log, uri, tdp, mode);
    }
    // Re-throw other errors
    throw error;
  }
};

/**
 * Fallback: fetch proof data via external CLI process.
 * Used when `import Paperproof` is not present in the user's file.
 */
const fetchViaCliFallback = async (
  log: vscode.OutputChannel,
  uri: string,
  tdp: TextDocumentPositionParams,
  mode: string
): Promise<ProofState> => {
  const filePath = uriToPath(uri);
  const line = tdp.position.line;
  const column = tdp.position.character;

  const result = await fetchViaExternalProcess(log, filePath, line, column, mode);

  if (result.error) {
    throw new Error(result.error);
  }

  return {
    goal: null, // CLI doesn't provide interactive goals
    proofTree: result.steps,
    version: result.version ?? undefined
  };
};

export default fetchLeanData;
