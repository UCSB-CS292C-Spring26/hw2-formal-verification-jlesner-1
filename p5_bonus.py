"""
CS292C Homework 2 — Problem 5 (Bonus): Verified Skill Composition (10 points)
===============================================================================
Verify that two sequentially composed agent skills maintain a filesystem
invariant, then show how a composition bug breaks the invariant.
"""

from z3 import *


# ============================================================================
# Filesystem Model
#
# We model the filesystem as a Z3 array: Array(Int, Int)
#   - Index = file path ID (integer)
#   - Value = content hash (integer)
#
# Two paths are special:
#   INPUT_FILE = 0   (the file Skill A reads)
#   OUTPUT_FILE = 1  (the file Skill B writes to)
# ============================================================================

INPUT_FILE = 0
OUTPUT_FILE = 1


# ============================================================================
# Part (a): Verify correct composition — 4 pts
#
# Skill A: Reads INPUT_FILE, extracts URLs. Does NOT modify any file.
#   Pre:  true
#   Post: fs_after_A = fs_before_A  (filesystem unchanged)
#
# Skill B: Fetches URLs and writes results to OUTPUT_FILE. Does NOT modify
#          any file other than OUTPUT_FILE.
#   Pre:  true
#   Post: Select(fs_after_B, OUTPUT_FILE) = result_content
#         ∧ ∀p. p ≠ OUTPUT_FILE → Select(fs_after_B, p) = Select(fs_before_B, p)
#
# Composed postcondition:
#   Select(fs_final, INPUT_FILE) = Select(fs_initial, INPUT_FILE)  [input preserved]
#   ∧ Select(fs_final, OUTPUT_FILE) = result_content               [output written]
#   ∧ ∀p. p ≠ OUTPUT_FILE → Select(fs_final, p) = Select(fs_initial, p)
#                                                                  [nothing else changed]
# ============================================================================

def verify_correct_composition():
    print("=== Part (a): Correct Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    # Skill A postcondition: filesystem unchanged
    skill_A_post = fs_after_A == fs_initial

    # Skill B postcondition: only OUTPUT_FILE changes (relative to fs_after_A)
    skill_B_post = And(
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Composed postcondition to verify
    composed_post = And(
        # Input file preserved
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        # Output written
        Select(fs_final, OUTPUT_FILE) == result_content,
        # Nothing else changed
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Check that (skill_A_post ∧ skill_B_post) → composed_post is valid.
    # By the duality from Lecture 7, a formula φ is valid iff ¬φ is unsat.
    # So we assert the premises and the negation of the conclusion, then check for UNSAT.
    s = Solver()
    s.add(skill_A_post)
    s.add(skill_B_post)
    s.add(Not(composed_post))

    result = s.check()

    if result == unsat:
        print("  Result: UNSAT")
        print("  => The implication is VALID.")
        print("  => Composed postcondition holds. Composition is correct.")
    elif result == sat:
        print("  Result: SAT (unexpected!)")
        print("  Counterexample:")
        print(f"    {s.model()}")
    else:
        print(f"  Result: {result}")
    print()


# ============================================================================
# Part (b): Buggy composition — 3 pts
#
# Bug: Skill B accidentally writes to INPUT_FILE instead of OUTPUT_FILE.
#
# Buggy Skill B postcondition:
#   Select(fs_final, INPUT_FILE) = result_content     ← overwrites input!
#   ∧ ∀p. p ≠ INPUT_FILE → Select(fs_final, p) = Select(fs_after_A, p)
#
# The composed postcondition should FAIL because the input file is modified.
# ============================================================================

def verify_buggy_composition():
    print("=== Part (b): Buggy Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    skill_A_post = fs_after_A == fs_initial

    # BUGGY Skill B: writes to INPUT_FILE instead of OUTPUT_FILE
    buggy_B_post = And(
        Select(fs_final, INPUT_FILE) == result_content,  # ← BUG
        ForAll([p], Implies(p != INPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Same composed postcondition as before
    composed_post = And(
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Check that the composed postcondition FAILS.
    # We assert the premises and the negation of the goal. If the result is SAT, Z3 hands us a state where the buggy skills satisfy their own postconditions but the composed contract is broken.
    s = Solver()
    s.add(skill_A_post)
    s.add(buggy_B_post)
    s.add(Not(composed_post))

    result = s.check()

    if result == sat:
        print("  Result: SAT")
        print("  => The implication is INVALID. Bug confirmed.")
        m = s.model()

        # Pull out the concrete witness so the failure is easy to read.
        initial_input  = m.eval(Select(fs_initial, INPUT_FILE),  model_completion=True)
        initial_output = m.eval(Select(fs_initial, OUTPUT_FILE), model_completion=True)
        final_input    = m.eval(Select(fs_final,   INPUT_FILE),  model_completion=True)
        final_output   = m.eval(Select(fs_final,   OUTPUT_FILE), model_completion=True)
        result_val     = m.eval(result_content, model_completion=True)

        print("  Counterexample:")
        print(f"    result_content                 = {result_val}")
        print(f"    fs_initial[INPUT_FILE]         = {initial_input}")
        print(f"    fs_initial[OUTPUT_FILE]        = {initial_output}")
        print(f"    fs_final[INPUT_FILE]           = {final_input}")
        print(f"    fs_final[OUTPUT_FILE]          = {final_output}")
        print()
        print("  Why this fails:")
        print("    The contract requires fs_final[INPUT_FILE] == fs_initial[INPUT_FILE].")
        print("    But buggy Skill B wrote result_content to INPUT_FILE, so the input")
        print("    got clobbered. OUTPUT_FILE was never touched, so the second clause")
        print("    of the contract also fails.")
    elif result == unsat:
        print("  Result: UNSAT (unexpected!)")
        print("  => The buggy composition somehow satisfies the contract.")
    else:
        print(f"  Result: {result}")
    print()


# ============================================================================
# Part (c): Real-world connection — 3 pts
#
# [EXPLANATION]
# This bug shows up all the time when you chain agent skills that share a working directory. A common case in Claude Code: one skill reads a config file to figure out what to do, and a later skill in the same run writes its output using a path that looks correct but resolves to that same config file. Maybe both paths come from a template, or maybe the second skill picks the "first matching file" and lands on the input by accident. The agent reports success because each skill met its own postcondition, but the input file is now corrupt and the next run reads garbage.
#
# A runtime monitor (Lecture 10) would catch this with an ordering and write-target rule: track every path read by an upstream skill, then deny any downstream write whose target path matches one of those reads unless the skill explicitly declares it as an output. That is the same kind of DFA monitor we built in Problem 4, just keyed on file paths instead of tool names. The monitor refuses the write before the filesystem changes, so the input stays intact even when the agent's plan is wrong.
# ============================================================================


# ============================================================================
if __name__ == "__main__":
    verify_correct_composition()
    verify_buggy_composition()