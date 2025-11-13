import asyncio
import json
import logging
import os
import re
import sys
from datetime import datetime
from difflib import unified_diff
from pathlib import Path
from typing import Dict, List, Optional

import aristotlelib
from aristotlelib.api_request import get_api_key
from rich.console import Console
from rich.syntax import Syntax
from rich.panel import Panel
from rich.table import Table
from tqdm import tqdm

class TqdmLoggingHandler(logging.Handler):
    """Custom logging handler that updates tqdm and writes to file."""
    
    def __init__(self, log_file: Path, progress_bar: Optional[tqdm] = None):
        super().__init__()
        self.log_file = log_file
        self.progress_bar = progress_bar
        self.log_file.parent.mkdir(parents=True, exist_ok=True)
        
    def emit(self, record):
        """Process log record and update progress bar."""
        try:
            msg = self.format(record)
            
            # Write to file
            with open(self.log_file, 'a') as f:
                f.write(f"{msg}\n")
            
            # Update progress bar if available
            if self.progress_bar is not None:
                # Look for percent complete in message
                match = re.search(r'percent complete:\s*(\d+)', msg)
                if match:
                    percent = int(match.group(1))
                    self.progress_bar.n = percent
                    self.progress_bar.refresh()
                
                # Update description based on status
                if "Creating project" in msg:
                    self.progress_bar.set_description("Creating project")
                elif "Adding imports" in msg:
                    self.progress_bar.set_description("Uploading imports")
                elif "solve" in msg.lower():
                    self.progress_bar.set_description("Solving proofs")
                elif "IN_PROGRESS" in msg:
                    self.progress_bar.set_description("Proving theorems")
        except Exception:
            self.handleError(record)

class ProofLogParser:
    """Parse structured proof log files."""
    
    DELIMITERS = {
        'input_start': '='*60 + '\nINPUT FILE CONTENTS\n' + '='*60,
        'input_end': '='*60 + '\nEND INPUT FILE CONTENTS\n' + '='*60,
        'log_start': '='*60 + '\nPROOF EXECUTION LOG\n' + '='*60,
        'log_end': '='*60 + '\nEND PROOF EXECUTION LOG\n' + '='*60,
        'summary_start': '='*60 + '\nPROOF SUMMARY\n' + '='*60,
        'output_start': '='*60 + '\nOUTPUT FILE CONTENTS\n' + '='*60,
        'output_end': '='*60 + '\nEND OUTPUT FILE CONTENTS\n' + '='*60,
        'notes_start': '='*60 + '\nUSER NOTES\n' + '='*60,
        'notes_end': '='*60 + '\nEND USER NOTES\n' + '='*60,
    }
    
    @staticmethod
    def parse_log_file(log_path: Path) -> Dict:
        """Parse a proof log file into structured data."""
        with open(log_path, 'r') as f:
            content = f.read()
        
        result = {
            'log_file': str(log_path),
            'metadata': {},
            'input_content': None,
            'output_content': None,
            'execution_log': None,
            'summary': {},
            'user_notes': None,
        }
        
        # Parse metadata (first section)
        meta_section = content.split('='*60)[0:2]
        if len(meta_section) > 1:
            for line in meta_section[1].strip().split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    result['metadata'][key.strip().lower().replace(' ', '_')] = value.strip()
        
        # Extract input content
        input_match = re.search(
            re.escape(ProofLogParser.DELIMITERS['input_start']) + r'\n(.*?)\n' + 
            re.escape(ProofLogParser.DELIMITERS['input_end']),
            content, re.DOTALL
        )
        if input_match:
            result['input_content'] = input_match.group(1)
        
        # Extract execution log
        log_match = re.search(
            re.escape(ProofLogParser.DELIMITERS['log_start']) + r'\n(.*?)\n' + 
            re.escape(ProofLogParser.DELIMITERS['log_end']),
            content, re.DOTALL
        )
        if log_match:
            result['execution_log'] = log_match.group(1)
        
        # Extract summary
        summary_match = re.search(
            re.escape(ProofLogParser.DELIMITERS['summary_start']) + r'\n(.*?)\n' + '='*60,
            content, re.DOTALL
        )
        if summary_match:
            for line in summary_match.group(1).strip().split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    result['summary'][key.strip().lower().replace(' ', '_')] = value.strip()
        
        # Extract output content
        output_match = re.search(
            re.escape(ProofLogParser.DELIMITERS['output_start']) + r'\n(.*?)\n' + 
            re.escape(ProofLogParser.DELIMITERS['output_end']),
            content, re.DOTALL
        )
        if output_match:
            result['output_content'] = output_match.group(1)
        
        # Extract user notes
        notes_match = re.search(
            re.escape(ProofLogParser.DELIMITERS['notes_start']) + r'\n(.*?)\n' + 
            re.escape(ProofLogParser.DELIMITERS['notes_end']),
            content, re.DOTALL
        )
        if notes_match:
            result['user_notes'] = notes_match.group(1)
        
        return result
    
    @staticmethod
    def extract_user_ratings(user_notes: str) -> Dict:
        """Extract structured ratings from user notes."""
        if not user_notes:
            return {}
        
        ratings = {}
        
        # Extract rating section
        rating_match = re.search(r'\[RATING\](.*?)\[', user_notes, re.DOTALL)
        if rating_match:
            rating_text = rating_match.group(1)
            ratings['ratings'] = {}
            for line in rating_text.strip().split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    ratings['ratings'][key.strip()] = value.strip()
        
        # Extract performance section
        perf_match = re.search(r'\[PERFORMANCE\](.*?)\[', user_notes, re.DOTALL)
        if perf_match:
            perf_text = perf_match.group(1)
            ratings['performance'] = {}
            for line in perf_text.strip().split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    ratings['performance'][key.strip()] = value.strip()
        
        # Extract feedback section
        feedback_match = re.search(r'\[FEEDBACK\](.*)', user_notes, re.DOTALL)
        if feedback_match:
            ratings['feedback'] = feedback_match.group(1).strip()
        
        return ratings
    
    @staticmethod
    def list_logs(logs_dir: str = "logs") -> List[Path]:
        """List all proof log files."""
        logs_path = Path(logs_dir)
        if not logs_path.exists():
            return []
        return sorted(logs_path.glob("proof_*.txt"), key=lambda p: p.stat().st_mtime, reverse=True)
    
    @staticmethod
    def display_log_summary(log_data: Dict):
        """Display a summary of a parsed log."""
        print(f"\nLog: {Path(log_data['log_file']).name}")
        print("="*60)
        
        if log_data['metadata']:
            print("\nMetadata:")
            for key, value in log_data['metadata'].items():
                print(f"  {key}: {value}")
        
        if log_data['summary']:
            print("\nSummary:")
            for key, value in log_data['summary'].items():
                print(f"  {key}: {value}")
        
        print(f"\nHas input: {log_data['input_content'] is not None}")
        print(f"Has output: {log_data['output_content'] is not None}")
        print(f"Has user notes: {log_data['user_notes'] is not None}")
        
        if log_data['user_notes']:
            ratings = ProofLogParser.extract_user_ratings(log_data['user_notes'])
            if ratings:
                print("\nUser Ratings:")
                if 'ratings' in ratings:
                    for key, value in ratings['ratings'].items():
                        print(f"  {key}: {value if value else '[Not filled]'}")
    
    @staticmethod
    def display_diff(log_data: Dict, use_pager: bool = True):
        """Display a beautiful diff between input and output files."""
        if not log_data['input_content'] or not log_data['output_content']:
            print("Cannot show diff: missing input or output content")
            return
        
        input_lines = log_data['input_content'].splitlines(keepends=True)
        output_lines = log_data['output_content'].splitlines(keepends=True)
        
        # Generate unified diff
        diff_lines = list(unified_diff(
            input_lines,
            output_lines,
            fromfile='input.lean',
            tofile='output.lean',
            lineterm=''
        ))
        
        if not diff_lines:
            print("✓ No differences found (files are identical)")
            return
        
        console = Console()
        
        # Count changes
        additions = sum(1 for line in diff_lines if line.startswith('+') and not line.startswith('+++'))
        deletions = sum(1 for line in diff_lines if line.startswith('-') and not line.startswith('---'))
        
        # Combine diff lines into a single string
        diff_text = ''.join(diff_lines)
        
        # Display with syntax highlighting in pager
        if use_pager:
            # Configure pager to disable mouse (less -K disables mouse input)
            # Save original pager setting
            original_pager = os.environ.get('PAGER')
            os.environ['PAGER'] = 'less -K -R'
            
            try:
                with console.pager(styles=True):
                    # Display header
                    console.print(Panel(
                        f"[bold cyan]Diff: {Path(log_data['log_file']).name}[/bold cyan]\n"
                        f"Status: [bold green]{log_data['summary'].get('status', 'UNKNOWN')}[/bold green]",
                        title="Proof Diff",
                        border_style="cyan"
                    ))
                    console.print()
                    
                    # Display with syntax highlighting
                    syntax = Syntax(
                        diff_text,
                        "diff",
                        theme="monokai",
                        line_numbers=True,
                        word_wrap=False
                    )
                    console.print(syntax)
                    
                    console.print()
                    console.print(f"[green]+{additions}[/green] additions, [red]-{deletions}[/red] deletions")
            finally:
                # Restore original pager setting
                if original_pager:
                    os.environ['PAGER'] = original_pager
                else:
                    os.environ.pop('PAGER', None)
        else:
            # Display without pager
            console.print(Panel(
                f"[bold cyan]Diff: {Path(log_data['log_file']).name}[/bold cyan]\n"
                f"Status: [bold green]{log_data['summary'].get('status', 'UNKNOWN')}[/bold green]",
                title="Proof Diff",
                border_style="cyan"
            ))
            
            syntax = Syntax(
                diff_text,
                "diff",
                theme="monokai",
                line_numbers=True,
                word_wrap=False
            )
            console.print(syntax)
            
            console.print(f"\n[green]+{additions}[/green] additions, [red]-{deletions}[/red] deletions")

class Theoros:
    """Aristotle theorem prover with integrated progress tracking and logging."""
    
    def __init__(self, api_key: Optional[str] = None, logs_dir: str = "logs"):
        """
        Initialize Theoros.
        
        Args:
            api_key: Aristotle API key (uses env var if not provided)
            logs_dir: Directory to store log files
        """
        # Get API key from parameter, environment, or raise error
        if api_key:
            self.api_key = api_key
            aristotlelib.set_api_key(api_key)
        else:
            # Try to get from environment or existing setting
            try:
                self.api_key = get_api_key()
            except ValueError:
                raise ValueError(
                    "No API key provided. Set ARISTOTLE_API_KEY environment variable "
                    "or pass api_key parameter"
                )
        
        self.logs_dir = Path(logs_dir)
        self.logs_dir.mkdir(exist_ok=True)
        
    def _setup_logging(self, log_file: Path, progress_bar: Optional[tqdm] = None) -> logging.Handler:
        """Setup logging with file output and tqdm integration."""
        handler = TqdmLoggingHandler(log_file, progress_bar)
        handler.setLevel(logging.INFO)
        formatter = logging.Formatter("%(levelname)s - %(message)s")
        handler.setFormatter(formatter)
        
        # Get aristotlelib logger and add handler
        logger = logging.getLogger("aristotlelib")
        logger.setLevel(logging.INFO)
        logger.addHandler(handler)
        
        # Also capture root logger
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.INFO)
        root_logger.addHandler(handler)
        
        return handler
    
    async def prove(
        self,
        input_file: str,
        output_file: Optional[str] = None,
        show_progress: bool = True
    ) -> dict:
        """
        Prove theorems in a Lean file.
        
        Args:
            input_file: Path to Lean file with sorries
            output_file: Path for output (defaults to input_file with _proved suffix)
            show_progress: Show tqdm progress bar
            
        Returns:
            dict with status, output_file, log_file, and error (if any)
        """
        # Setup paths
        input_path = Path(input_file)
        if not input_path.exists():
            raise FileNotFoundError(f"Input file not found: {input_file}")
        
        if output_file is None:
            output_file = str(self.logs_dir / f"{input_path.stem}_proved.lean")
        
        # Create log file with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_file = self.logs_dir / f"proof_{input_path.stem}_{timestamp}.txt"
        
        # Read input file content
        with open(input_path, 'r') as f:
            input_content = f.read()
        
        # Write header to log file with input content
        with open(log_file, 'w') as f:
            f.write(f"Theoros Proof Log\n")
            f.write(f"{'='*60}\n")
            f.write(f"Input file: {input_file}\n")
            f.write(f"Output file: {output_file}\n")
            f.write(f"Started at: {datetime.now().isoformat()}\n")
            f.write(f"{'='*60}\n\n")
            
            # Write input file contents
            f.write(f"{'='*60}\n")
            f.write(f"INPUT FILE CONTENTS\n")
            f.write(f"{'='*60}\n")
            f.write(input_content)
            f.write(f"\n{'='*60}\n")
            f.write(f"END INPUT FILE CONTENTS\n")
            f.write(f"{'='*60}\n\n")
            
            f.write(f"{'='*60}\n")
            f.write(f"PROOF EXECUTION LOG\n")
            f.write(f"{'='*60}\n\n")
        
        print(f"Input:  {input_file}")
        print(f"Output: {output_file}")
        print(f"Logs:   {log_file}")
        print()
        
        # Setup progress bar
        progress_bar = None
        if show_progress:
            progress_bar = tqdm(
                total=100,
                desc="Initializing",
                unit="%",
                bar_format="{desc}: {percentage:3.0f}%|{bar}| {n:.0f}/{total:.0f}",
                leave=False
            )
        
        # Setup logging
        handler = self._setup_logging(log_file, progress_bar)
        
        result = {
            "status": "FAILED",
            "output_file": output_file,
            "log_file": str(log_file),
            "error": None
        }
        
        try:
            # Prove theorems
            output_path = await aristotlelib.Project.prove_from_file(
                input_file,
                output_file_path=output_file,
                wait_for_completion=True
            )
            
            if progress_bar:
                progress_bar.n = 100
                progress_bar.set_description("Complete")
                progress_bar.close()
            
            result["status"] = "COMPLETE"
            result["output_file"] = str(output_path)
            
            print("✓ Proof complete!")
            print(f"  Solution: {output_path}")
            
        except Exception as e:
            result["error"] = str(e)
            if progress_bar:
                progress_bar.set_description("Failed")
                progress_bar.close()
            print(f"\n✗ Proof failed: {e}")
        
        finally:
            # Cleanup already done in try/except blocks
            
            # Remove handler
            logger = logging.getLogger("aristotlelib")
            logger.removeHandler(handler)
            root_logger = logging.getLogger()
            root_logger.removeHandler(handler)
            
            # Write footer to log with output content and user notes section
            with open(log_file, 'a') as f:
                f.write(f"\n{'='*60}\n")
                f.write(f"END PROOF EXECUTION LOG\n")
                f.write(f"{'='*60}\n\n")
                
                f.write(f"{'='*60}\n")
                f.write(f"PROOF SUMMARY\n")
                f.write(f"{'='*60}\n")
                f.write(f"Completed at: {datetime.now().isoformat()}\n")
                f.write(f"Status: {result['status']}\n")
                if result['error']:
                    f.write(f"Error: {result['error']}\n")
                f.write(f"{'='*60}\n\n")
                
                # Write output file contents if successful
                if result['status'] == 'COMPLETE':
                    try:
                        with open(output_file, 'r') as out_f:
                            output_content = out_f.read()
                        
                        f.write(f"{'='*60}\n")
                        f.write(f"OUTPUT FILE CONTENTS\n")
                        f.write(f"{'='*60}\n")
                        f.write(output_content)
                        f.write(f"\n{'='*60}\n")
                        f.write(f"END OUTPUT FILE CONTENTS\n")
                        f.write(f"{'='*60}\n\n")
                    except Exception as e:
                        f.write(f"Note: Could not read output file: {e}\n\n")
                
                # Write user notes section with template
                f.write(f"{'='*60}\n")
                f.write(f"USER NOTES\n")
                f.write(f"{'='*60}\n")
                f.write(f"Instructions: Edit this section to add your evaluation\n\n")
                f.write(f"[RATING]\n")
                f.write(f"Overall Quality (1-5): \n")
                f.write(f"Correctness (1-5): \n")
                f.write(f"Elegance (1-5): \n\n")
                f.write(f"[PERFORMANCE]\n")
                f.write(f"Speed: \n")
                f.write(f"Time Taken: \n")
                f.write(f"Percent Complete When Finished: \n\n")
                f.write(f"[FEEDBACK]\n")
                f.write(f"What worked well:\n")
                f.write(f"\n\n")
                f.write(f"What could be improved:\n")
                f.write(f"\n\n")
                f.write(f"Suggestions for next iteration:\n")
                f.write(f"\n\n")
                f.write(f"Additional notes:\n")
                f.write(f"\n\n")
                f.write(f"{'='*60}\n")
                f.write(f"END USER NOTES\n")
                f.write(f"{'='*60}\n")
        
        return result


# ============================================================================
# CLI
# ============================================================================

def main():
    """Command-line interface."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Theoros - Prove Lean theorems with Aristotle and review logs',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Proving Examples:
  %(prog)s prove MyTheorem.lean
  %(prog)s prove MyTheorem.lean --output proved.lean
  %(prog)s prove MyTheorem.lean --no-progress
  %(prog)s prove MyTheorem.lean --api-key YOUR_KEY

Review Examples:
  %(prog)s review --list
  %(prog)s review --file logs/proof_MatrixLemmas_20251113_110633.txt
  %(prog)s review --file logs/proof_MatrixLemmas_20251113_110633.txt --export-json data.json
        """
    )
    
    subparsers = parser.add_subparsers(dest='command', help='Command to execute')
    
    # Prove subcommand
    prove_parser = subparsers.add_parser('prove', help='Prove theorems in a Lean file')
    prove_parser.add_argument(
        'input_file',
        help='Path to Lean file to prove'
    )
    prove_parser.add_argument(
        '--api-key',
        help='Aristotle API key (or set ARISTOTLE_API_KEY env var)',
        default=None
    )
    prove_parser.add_argument(
        '--output',
        dest='output_file',
        help='Path for output file (default: logs/INPUT_proved.lean)',
        default=None
    )
    prove_parser.add_argument(
        '--logs-dir',
        help='Directory for logs and output (default: logs/)',
        default='logs'
    )
    prove_parser.add_argument(
        '--no-progress',
        action='store_true',
        help='Disable progress bar'
    )
    
    # Review subcommand
    review_parser = subparsers.add_parser('review', help='Review proof logs')
    review_parser.add_argument(
        '--logs-dir',
        default='logs',
        help='Directory containing log files (default: logs/)'
    )
    review_parser.add_argument(
        '--list',
        action='store_true',
        help='List all log files'
    )
    review_parser.add_argument(
        '--file',
        help='Parse and display specific log file'
    )
    review_parser.add_argument(
        '--export-json',
        help='Export parsed logs to JSON file'
    )
    review_parser.add_argument(
        '--no-pager',
        action='store_true',
        help='Disable pager (print diff directly to terminal)'
    )
    
    args = parser.parse_args()
    
    # Handle prove command
    if args.command == 'prove':
        try:
            # Initialize prover
            prover = Theoros(api_key=args.api_key, logs_dir=args.logs_dir)
            
            # Run proof
            result = asyncio.run(prover.prove(
                input_file=args.input_file,
                output_file=args.output_file,
                show_progress=not args.no_progress
            ))
            
            # Exit with appropriate code
            sys.exit(0 if result["status"] == "COMPLETE" else 1)
            
        except Exception as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
    
    # Handle review command
    elif args.command == 'review':
        # List logs
        if args.list:
            logs = ProofLogParser.list_logs(args.logs_dir)
            if not logs:
                console = Console()
                console.print(f"[yellow]No log files found in {args.logs_dir}/[/yellow]")
                return
            
            console = Console()
            
            # Create a beautiful table
            table = Table(title=f"Proof Logs ({len(logs)} total)", show_header=True, header_style="bold cyan")
            table.add_column("File", style="white", no_wrap=False, width=50)
            table.add_column("Status", justify="center", width=12)
            table.add_column("Date", style="dim", width=20)
            
            for log in logs:
                data = ProofLogParser.parse_log_file(log)
                status = data['summary'].get('status', 'UNKNOWN')
                
                # Color code status
                if status == 'COMPLETE':
                    status_display = "[bold green]✓ COMPLETE[/bold green]"
                elif status == 'FAILED':
                    status_display = "[bold red]✗ FAILED[/bold red]"
                else:
                    status_display = f"[yellow]{status}[/yellow]"
                
                # Extract date from filename
                date_str = data['metadata'].get('started_at', '')
                if date_str:
                    try:
                        from datetime import datetime
                        dt = datetime.fromisoformat(date_str)
                        date_display = dt.strftime("%Y-%m-%d %H:%M:%S")
                    except:
                        date_display = date_str[:19] if len(date_str) >= 19 else date_str
                else:
                    date_display = "N/A"
                
                table.add_row(log.name, status_display, date_display)
            
            console.print(table)
            console.print(f"\n[dim]Use 'theoros.py review --file <filename>' to view a diff[/dim]")
            return
        
        # Parse specific file
        if args.file:
            log_path = Path(args.file)
            if not log_path.exists():
                print(f"Error: File not found: {args.file}")
                return
            
            data = ProofLogParser.parse_log_file(log_path)
            
            # Always show diff (with or without pager)
            ProofLogParser.display_diff(data, use_pager=not args.no_pager)
            
            if args.export_json:
                with open(args.export_json, 'w') as f:
                    json.dump(data, f, indent=2)
                print(f"\nExported to: {args.export_json}")
            return
        
        # Default: show all logs summary with table
        logs = ProofLogParser.list_logs(args.logs_dir)
        if not logs:
            console = Console()
            console.print(f"[yellow]No log files found in {args.logs_dir}/[/yellow]")
            return
        
        console = Console()
        
        # Create a beautiful table
        table = Table(title=f"Proof Logs ({len(logs)} total)", show_header=True, header_style="bold cyan")
        table.add_column("File", style="white", no_wrap=False, width=50)
        table.add_column("Status", justify="center", width=12)
        table.add_column("Date", style="dim", width=20)
        
        for log in logs:
            data = ProofLogParser.parse_log_file(log)
            status = data['summary'].get('status', 'UNKNOWN')
            
            # Color code status
            if status == 'COMPLETE':
                status_display = "[bold green]✓ COMPLETE[/bold green]"
            elif status == 'FAILED':
                status_display = "[bold red]✗ FAILED[/bold red]"
            else:
                status_display = f"[yellow]{status}[/yellow]"
            
            # Extract date from filename
            date_str = data['metadata'].get('started_at', '')
            if date_str:
                try:
                    dt = datetime.fromisoformat(date_str)
                    date_display = dt.strftime("%Y-%m-%d %H:%M:%S")
                except:
                    date_display = date_str[:19] if len(date_str) >= 19 else date_str
            else:
                date_display = "N/A"
            
            table.add_row(log.name, status_display, date_display)
        
        console.print(table)
        console.print(f"\n[dim]Use 'theoros.py review --file <filename>' to view a diff[/dim]")
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()

