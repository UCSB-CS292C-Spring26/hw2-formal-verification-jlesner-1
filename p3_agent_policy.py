"""
CS292C Homework 2 - Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy - 10 pts
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1-R5.

    Strategy: closed-world. We define `allowed(u, t, r)` to be true if and only
    if some rule explicitly permits it. This way we don't need a separate
    default-deny rule, the iff already gives us that behavior.

    R4 (no shell_exec on sensitive) is enforced by AND-ing `not is_sensitive(r)`
    into the admin's shell_exec permission, so it overrides R3 cleanly.
    R5 (network_fetch only in sandbox) is similarly AND-ed into the admin's
    network_fetch permission.
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # The big iff: allowed(u, t, r) holds exactly when one of the rule branches below fires. This single ForAll captures the entire policy under a closed-world assumption.
    constraints.append(ForAll([u, t, r],
        allowed(u, t, r) ==
        Or(
            # R1: Viewers may ONLY file_read non-sensitive resources.
            # Note: no other branch mentions viewers, so everything ele is automatically denied for them.
            And(role(u) == VIEWER,
                t == FILE_READ,
                Not(is_sensitive(r))),

            # R2a: Developers may file_read anything.
            And(role(u) == DEVELOPER,
                t == FILE_READ),

            # R2b: Developers may file_write resources they own or that are in the sandbox.
            And(role(u) == DEVELOPER,
                t == FILE_WRITE,
                Or(owner(r) == u, in_sandbox(r))),

            # R3 + R4: Admins may shell_exec only on non-sensitive resources.
            # R4 (nobody may shell_exec sensitive) is folded in here.
            And(role(u) == ADMIN,
                t == SHELL_EXEC,
                Not(is_sensitive(r))),

            # R3: Admins may file_read or file_write anything.
            And(role(u) == ADMIN,
                Or(t == FILE_READ, t == FILE_WRITE)),

            # R3 + R5: Admins may network_fetch, but only in sandbox.
            # R5 says network_fetch is "allowed only on sandbox resources", which we read as a constraint on when network_fetch is ever allowed, not a grant of network_fetch to non-admins. So only admins get network_fetch (via R3), and we fold R5 in here.
            And(role(u) == ADMIN,
                t == NETWORK_FETCH,
                in_sandbox(r)),
        )
    ))

    # Sanity constraint on roles: every user has one of the three roles.
    # This isn't strictly required by R1-R5 but keeps models meaningful.
    constraints.append(ForAll([u],
        Or(role(u) == ADMIN, role(u) == DEVELOPER, role(u) == VIEWER)))

    return constraints


# ============================================================================
# Part (b): Policy Queries - 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  -> {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    # Expected SAT: R2b allows file_write if owner OR in_sandbox.
    # Sensitivity doesn't restrict file_write for developers.
    u = Const('u_q1', User)
    r = Const('r_q1', Resource)
    other = Const('other_q1', User)
    query("Q1: developer writes sensitive file (not owner, in sandbox)?",
          policy,
          [role(u) == DEVELOPER,
           is_sensitive(r),
           in_sandbox(r),
           owner(r) == other,
           u != other,
           allowed(u, FILE_WRITE, r)])

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    # Expected UNSAT: R5 forbids network_fetch outside sandbox for everyone, including admins. The encoding folds this into the admin branch.
    u2 = Const('u_q2', User)
    r2 = Const('r_q2', Resource)
    query("Q2: admin network_fetch outside sandbox?",
          policy,
          [role(u2) == ADMIN,
           Not(in_sandbox(r2)),
           allowed(u2, NETWORK_FETCH, r2)])

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    # Expected UNSAT: R4 forbids this for everyone. We quantify over all roles by leaving role(u) free.
    u3 = Const('u_q3', User)
    r3 = Const('r_q3', Resource)
    query("Q3: any role can shell_exec a sensitive resource?",
          policy,
          [is_sensitive(r3),
           allowed(u3, SHELL_EXEC, r3)])

    # Q4: Remove R4 - what dangerous action becomes possible?
    #
    # [EXPLANATION] Without R4, admins regain unrestricted shell_exec on any resource (R3 alone). The dangerous action is: an admin running a shell command against a sensitive resource (e.g., a secrets file or a production config). Below we build a policy without the "Not(is_sensitive(r))" guard on the admin shell_exec branch and show that admin shell_exec on sensitive is now SAT, with a concrete model.
    print("--- Q4: policy without R4 ---")

    u4 = Const('u_q4', User)
    r4 = Const('r_q4', Resource)
    t4 = Int('t4')

    no_r4_policy = [
        ForAll([u4, t4, r4],
            allowed(u4, t4, r4) ==
            Or(
                And(role(u4) == VIEWER,
                    t4 == FILE_READ,
                    Not(is_sensitive(r4))),
                And(role(u4) == DEVELOPER,
                    t4 == FILE_READ),
                And(role(u4) == DEVELOPER,
                    t4 == FILE_WRITE,
                    Or(owner(r4) == u4, in_sandbox(r4))),
                # R4 dropped: admin shell_exec no longer guards against sensitive
                And(role(u4) == ADMIN,
                    t4 == SHELL_EXEC),
                And(role(u4) == ADMIN,
                    Or(t4 == FILE_READ, t4 == FILE_WRITE)),
                And(role(u4) == ADMIN,
                    t4 == NETWORK_FETCH,
                    in_sandbox(r4)),
            )),
        ForAll([u4],
            Or(role(u4) == ADMIN, role(u4) == DEVELOPER, role(u4) == VIEWER)),
    ]

    u4q = Const('u_q4q', User)
    r4q = Const('r_q4q', Resource)
    query("Q4: without R4, admin shell_exec on sensitive resource?",
          no_r4_policy,
          [role(u4q) == ADMIN,
           is_sensitive(r4q),
           allowed(u4q, SHELL_EXEC, r4q)])


# ============================================================================
# Part (c): Privilege Escalation - 7 pts
# ============================================================================

def part_c():
    """
    Add R6 (developers may shell_exec on non-sensitive sandbox resources),
    then model a 2-step trace where step 1's shell command flips r2's
    sensitivity flag from True to False, allowing step 2 to fire even
    though r2 was previously sensitive.

    Encoding: use two copies of is_sensitive (before/after) and two copies
    of `allowed` parameterized by which sensitivity snapshot they query.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    # Two snapshots of the world's sensitivity labelling.
    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after  = Function('is_sensitive_after',  Resource, BoolSort())

    # `allowed_t` is parameterized over a sensitivity predicate (passed in by snapshot). We re-encode the policy + R6 once per snapshot.
    allowed_before = Function('allowed_before', User, IntSort(), Resource, BoolSort())
    allowed_after  = Function('allowed_after',  User, IntSort(), Resource, BoolSort())

    def policy_with_r6(allowed_fn, sens_fn):
        u = Const('u_pc', User)
        r = Const('r_pc', Resource)
        t = Int('t_pc')
        return ForAll([u, t, r],
            allowed_fn(u, t, r) ==
            Or(
                And(role(u) == VIEWER, t == FILE_READ, Not(sens_fn(r))),
                And(role(u) == DEVELOPER, t == FILE_READ),
                And(role(u) == DEVELOPER, t == FILE_WRITE,
                    Or(owner(r) == u, in_sandbox(r))),
                # R6: developers may shell_exec on non-sensitive sandbox resources
                And(role(u) == DEVELOPER, t == SHELL_EXEC,
                    Not(sens_fn(r)), in_sandbox(r)),
                And(role(u) == ADMIN, t == SHELL_EXEC, Not(sens_fn(r))),
                And(role(u) == ADMIN, Or(t == FILE_READ, t == FILE_WRITE)),
                And(role(u) == ADMIN, t == NETWORK_FETCH, in_sandbox(r)),
            ))

    base = [
        policy_with_r6(allowed_before, is_sensitive_before),
        policy_with_r6(allowed_after,  is_sensitive_after),
        ForAll([Const('u_role', User)],
            Or(role(Const('u_role', User)) == ADMIN,
               role(Const('u_role', User)) == DEVELOPER,
               role(Const('u_role', User)) == VIEWER)),
    ]

    # The attack trace.
    dev = Const('dev', User)
    r1 = Const('r1', Resource)   # the lever: non-sensitive sandbox resource
    r2 = Const('r2', Resource)   # the target: was sensitive, becomes non-sensitive

    attack = [
        # Developer is a developer.
        role(dev) == DEVELOPER,

        # Step 1: shell_exec on r1 (non-sensitive sandbox), allowed by R6.
        Not(is_sensitive_before(r1)),
        in_sandbox(r1),
        allowed_before(dev, SHELL_EXEC, r1),

        # Side effect: r1's sensitivity is unchanged (it stays non-sensitive), but r2's sensitivity flips from True to False.
        is_sensitive_before(r2),         # r2 starts sensitive
        Not(is_sensitive_after(r2)),     # r2 ends non-sensitive
        # r1 unchanged across the two snapshots.
        is_sensitive_after(r1) == is_sensitive_before(r1),
        in_sandbox(r2),                  # r2 is in the sandbox

        # Step 2: shell_exec on r2 in the AFTER snapshot. Now allowed because r2 is no longer sensitive.
        allowed_after(dev, SHELL_EXEC, r2),

        # The escalation: in the BEFORE snapshot the developer could NOT shell_exec r2 (it was sensitive). We assert this to make the attack meaningful, otherwise step 2 would already have been legal.
        Not(allowed_before(dev, SHELL_EXEC, r2)),
    ]

    print("--- Escalation check (no fix) ---")
    s = Solver()
    s.add(base + attack)
    result = s.check()
    print(f"  Result: {result}")
    if result == sat:
        m = s.model()
        print(f"  Attack succeeds. Model:\n    {m}")
        print("  Interpretation: the developer used a permitted shell_exec")
        print("  on r1 to flip r2's sensitivity, then shell_exec'd r2 even")
        print("  though r2 was sensitive at the start. R4 is bypassed across")
        print("  the two-step trace.\n")
    else:
        print("  No attack found (unexpected).\n")

    # ------------------------------------------------------------------
    # The fix.
    # ------------------------------------------------------------------
    # [EXPLANATION] The escalation works because we trust the AFTER snapshot for the sensitivity check on step 2, but the dangerous data is the same data that was sensitive in the BEFORE snapshot. The cleanest fix is "sticky sensitivity": once a resource has ever been marked sensitive in the trace, it remains sensitive for permission checks for the rest of the trace. We encode this as: for the step-2 permission check, treat r as sensitive if it was sensitive in EITHER snapshot. Equivalently, we add the constraint that the policy in the AFTER snapshot must use is_sensitive_before OR is_sensitive_after when deciding shell_exec. Concrete implementation: define a fixed allowed_after_fixed that checks `is_sensitive_before(r) OR is_sensitive_after(r)` for the shell_exec branch. This blocks the attack because r2 was sensitive before, so even after the flip, shell_exec on r2 stays denied.

    print("--- Escalation check (with fix: sticky sensitivity) ---")

    allowed_after_fixed = Function('allowed_after_fixed',
                                    User, IntSort(), Resource, BoolSort())

    def policy_sticky(allowed_fn):
        u = Const('u_fix', User)
        r = Const('r_fix', Resource)
        t = Int('t_fix')
        # Sticky: a resource is "effectively sensitive" if it was ever
        # sensitive across the trace.
        eff_sens = lambda x: Or(is_sensitive_before(x), is_sensitive_after(x))
        return ForAll([u, t, r],
            allowed_fn(u, t, r) ==
            Or(
                And(role(u) == VIEWER, t == FILE_READ, Not(eff_sens(r))),
                And(role(u) == DEVELOPER, t == FILE_READ),
                And(role(u) == DEVELOPER, t == FILE_WRITE,
                    Or(owner(r) == u, in_sandbox(r))),
                And(role(u) == DEVELOPER, t == SHELL_EXEC,
                    Not(eff_sens(r)), in_sandbox(r)),
                And(role(u) == ADMIN, t == SHELL_EXEC, Not(eff_sens(r))),
                And(role(u) == ADMIN, Or(t == FILE_READ, t == FILE_WRITE)),
                And(role(u) == ADMIN, t == NETWORK_FETCH, in_sandbox(r)),
            ))

    fixed_base = [
        policy_with_r6(allowed_before, is_sensitive_before),
        policy_sticky(allowed_after_fixed),
        ForAll([Const('u_role2', User)],
            Or(role(Const('u_role2', User)) == ADMIN,
               role(Const('u_role2', User)) == DEVELOPER,
               role(Const('u_role2', User)) == VIEWER)),
    ]

    fixed_attack = [
        role(dev) == DEVELOPER,
        Not(is_sensitive_before(r1)),
        in_sandbox(r1),
        allowed_before(dev, SHELL_EXEC, r1),
        is_sensitive_before(r2),
        Not(is_sensitive_after(r2)),
        is_sensitive_after(r1) == is_sensitive_before(r1),
        in_sandbox(r2),
        # Try to perform step 2 under the fixed policy.
        allowed_after_fixed(dev, SHELL_EXEC, r2),
    ]

    s2 = Solver()
    s2.add(fixed_base + fixed_attack)
    result2 = s2.check()
    print(f"  Result: {result2}")
    if result2 == unsat:
        print("  ESCALATION BLOCKED")
    else:
        print("  Fix failed; attack still succeeds:")
        print(f"    {s2.model()}")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()