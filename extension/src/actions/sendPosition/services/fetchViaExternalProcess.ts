import * as vscode from "vscode";
import * as cp from "child_process";
import * as path from "path";
import { promisify } from "util";

const execFile = promisify(cp.execFile);

interface CliResult {
  steps: any[];
  version?: number;
  error?: string;
}

/**
 * Finds the workspace root containing the given file.
 * Falls back to the file's directory if no workspace is found.
 */
const findWorkspaceRoot = (filePath: string): string => {
  const workspaceFolder = vscode.workspace.getWorkspaceFolders()?.find(
    folder => filePath.startsWith(folder.uri.fsPath)
  );
  return workspaceFolder?.uri.fsPath ?? path.dirname(filePath);
};

/**
 * Fetches proof data by spawning `lake exe paperproof-cli` as an external process.
 * This is the fallback when the RPC method is not available (no `import Paperproof` in the file).
 */
const fetchViaExternalProcess = async (
  log: vscode.OutputChannel,
  filePath: string,
  line: number,
  column: number,
  mode: string
): Promise<CliResult> => {
  const workspaceRoot = findWorkspaceRoot(filePath);

  log.appendLine(`CLI fallback: lake exe paperproof-cli --by-position "${filePath}" ${line} ${column} ${mode}`);
  log.appendLine(`Working directory: ${workspaceRoot}`);

  try {
    const { stdout, stderr } = await execFile(
      "lake",
      ["exe", "paperproof-cli", "--by-position", filePath, String(line), String(column), mode],
      {
        cwd: workspaceRoot,
        timeout: 60000, // 60 second timeout
        maxBuffer: 10 * 1024 * 1024, // 10MB buffer for large proofs
      }
    );

    if (stderr) {
      log.appendLine(`CLI stderr: ${stderr}`);
    }

    if (!stdout.trim()) {
      return { steps: [], error: "Empty response from CLI" };
    }

    log.appendLine(`CLI stdout (first 500 chars): ${stdout.substring(0, 500)}`);

    const result = JSON.parse(stdout);

    if (result.error) {
      return { steps: [], error: result.error };
    }

    return result;
  } catch (error: any) {
    // Check for common errors
    if (error.code === "ENOENT") {
      return {
        steps: [],
        error: "lake command not found. Make sure Lean/Lake is installed and in PATH."
      };
    }

    if (error.killed || error.signal === "SIGTERM") {
      return {
        steps: [],
        error: "CLI process timed out. The file may be too large or complex."
      };
    }

    // Try to parse JSON from stdout even on error (CLI might have output valid JSON with error)
    if (error.stdout) {
      try {
        const result = JSON.parse(error.stdout);
        if (result.error) {
          return { steps: [], error: result.error };
        }
      } catch {
        // Ignore JSON parse errors
      }
    }

    const errorMessage = error.stderr || error.message || String(error);
    log.appendLine(`CLI error: ${errorMessage}`);

    return {
      steps: [],
      error: `CLI failed: ${errorMessage}`
    };
  }
};

export default fetchViaExternalProcess;
