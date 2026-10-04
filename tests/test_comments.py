"""Comments follow their declarations when source commands are moved or replaced."""

import os
import unittest
from unittest.mock import patch

from lean_merge import merge, normalize


def setUpModule():
    environment = patch.dict(os.environ, {"LEAN_TOOL_FAILURE_ARCHIVE": "0"})
    environment.start()
    unittest.addModuleCleanup(environment.stop)


class CommentTests(unittest.TestCase):
    def test_target_restores_base_comments_and_discards_extraction_leftovers(self):
        helper = "-- Helper explanation.\ntheorem helper : True := True.intro\n"
        comment = "-- 目标说明\n/- Outer /- nested -/ comment. -/\n"
        doc = "/-- Target documentation. -/\n@[simp] "
        base = (helper + comment + doc + "theorem target : True := sorry\n"
                "-- Sibling explanation.\ntheorem sibling : True := True.intro\n")
        # Extraction can leave comments from removed declarations before the target.
        donor = ("-- Helper explanation.\n\n-- Sibling explanation.\n\n" + comment +
                 "/-- Donor documentation. -/\ntheorem solution : True := by\n"
                 "  -- Keep the proof comment.\n  trivial\n")
        for newline in ("\n", "\r\n"):
            with self.subTest(newline=newline):
                result = merge(base.replace("\n", newline), donor,
                               target="target", proof="solution")
                output = result["content"]
                self.assertTrue(result["verified"])
                for marker in ("-- Helper explanation.", "-- Sibling explanation.",
                               "-- 目标说明", "/- Outer", "Target documentation.",
                               "-- Keep the proof comment."):
                    self.assertEqual(output.count(marker), 1, output)
                self.assertIn((comment + doc + "theorem _root_.target").replace("\n", newline),
                              output)
                self.assertNotIn("Donor documentation.", output)
                if newline == "\r\n":
                    self.assertNotIn("\n", output.replace("\r\n", ""))

    def test_lifted_comments_and_footer_appear_once(self):
        base = ("-- Namespace explanation.\nnamespace N\n"
                "-- Context explanation.\nvariable (n : Nat)\n"
                "-- Helper explanation.\ntheorem helper : n = n := rfl -- Inline helper.\n"
                "-- Target explanation.\ntheorem target : n = n := sorry\n"
                "theorem sibling : n = n := rfl\nend N\n-- File footer.\n")
        donor = ("namespace N\ntheorem helper (n : Nat) : n = n := rfl\n"
                 "theorem target (n : Nat) : n = n := helper n\nend N\n")
        output = merge(base, donor, target="N.target", proof="N.target")["content"]
        for marker in ("Namespace", "Context", "Helper", "Inline helper", "Target", "File footer"):
            self.assertEqual(output.count(marker), 1, output)
        self.assertIn("-- Helper explanation.\ntheorem helper : n = n := rfl -- Inline helper.", output)
        self.assertIn("-- Target explanation.\ntheorem target", output)
        self.assertTrue(output.rstrip().endswith("-- File footer."))

    def test_equal_comments_on_different_declarations_are_preserved(self):
        output = merge(
            "-- Explanation.\ntheorem target : True := sorry\n"
            "-- Explanation.\ntheorem sibling : True := True.intro\n",
            "-- Explanation.\ntheorem helper : True := True.intro\n"
            "-- Explanation.\ntheorem target : True := helper\n",
            target="target", proof="target")["content"]
        self.assertEqual(output.count("-- Explanation."), 3, output)

    def test_target_explanation_left_before_inserted_helper_is_moved_back(self):
        comment = "-- Main counting argument.\n-- Each row contributes once.\n"
        output = merge(
            comment + "theorem target : True := sorry\n",
            comment + "private theorem helper : True := True.intro\n"
            "theorem target : True := helper\n",
            target="target", proof="target")["content"]
        self.assertEqual(output.count(comment), 1, output)
        self.assertIn(comment + "theorem target", output)

    def test_helper_comment_containing_target_explanation_is_not_removed(self):
        comment = "-- Main counting argument.\n"
        helper_comment = comment + "-- Extra helper detail.\n"
        output = merge(
            comment + "theorem target : True := sorry\n",
            helper_comment + "theorem helper : True := True.intro\n"
            "theorem target : True := helper\n",
            target="target", proof="target")["content"]
        self.assertIn(helper_comment + "theorem helper", output)
        self.assertIn(comment + "theorem target", output)

    def test_donor_footer_drops_only_an_exact_copy_of_a_base_explanation(self):
        sibling_comment = "-- Sibling explanation.\n-- Second line.\n"
        base = ("theorem target : True := sorry\n" + sibling_comment +
                "theorem sibling : True := True.intro\n")
        for tail in (sibling_comment, "-- Independent donor footer.\n"):
            with self.subTest(tail=tail):
                output = merge(base, "theorem target : True := True.intro\n\n" + tail,
                               target="target", proof="target")["content"]
                self.assertEqual(output.count(sibling_comment), 1, output)
                self.assertEqual(output.count(tail), 1, output)

    def test_normalize_does_not_attach_removed_inline_comment_to_target(self):
        output = normalize(
            "def unused := 0 -- Only unused.\n"
            "-- Target explanation.\ntheorem target : True := by\n"
            "  let s := \"-- Not a comment /- either -/\"\n"
            "  trivial -- Proof ending.\n-- File footer.\n",
            target="target")["content"]
        self.assertNotIn("Only unused", output)
        self.assertIn("-- Target explanation.\ntheorem target", output)
        self.assertIn('"-- Not a comment /- either -/"', output)
        self.assertIn("trivial -- Proof ending.", output)
        self.assertEqual(output.count("-- File footer."), 1)

    def test_mutual_target_comments_move_with_theorem(self):
        output = merge(
            "mutual\n-- Sibling explanation.\ntheorem sibling : True := True.intro\n"
            "-- Target explanation.\n/- Target block. -/\ntheorem target : True := sorry\nend\n",
            "-- Donor explanation.\ntheorem solution : True := True.intro\n",
            target="target", proof="solution")["content"]
        self.assertIn("-- Target explanation.\n/- Target block. -/\ntheorem _root_.target", output)
        self.assertEqual(output.count("Target explanation"), 1)
        self.assertEqual(output.count("Sibling explanation"), 1)
        self.assertNotIn("Donor explanation", output)

    def test_multiline_inline_block_stays_with_lifted_helper(self):
        helper = ("theorem helper : True := True.intro /- Inline α\n"
                  "  /- nested -/\n  end of block. -/\n")
        output = merge(
            helper + "-- Target explanation.\ntheorem target : True := sorry\n",
            "theorem helper : True := True.intro\n"
            "theorem target : True := helper -- Last line without newline.",
            target="target", proof="target")["content"]
        self.assertIn(helper, output)
        self.assertEqual(output.count("Inline α"), 1)
        self.assertIn("-- Target explanation.\ntheorem target", output)
        self.assertIn("helper -- Last line without newline.\n", output)

    def test_declarations_only_discards_reused_declaration_comments(self):
        output = merge(
            "-- Shared explanation.\ntheorem helper : True := True.intro\n",
            "-- Shared explanation.\ntheorem helper : True := True.intro -- Donor inline.\n"
            "-- New explanation.\ntheorem added : True := helper\n",
            declarations_only=True)["content"]
        self.assertEqual(output.count("-- Shared explanation."), 1)
        self.assertNotIn("Donor inline", output)
        self.assertIn("-- New explanation.\ntheorem added", output)


if __name__ == "__main__":
    unittest.main()
