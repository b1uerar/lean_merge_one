"""Regressions for moving original commands without printing proof expressions."""

import os
import unittest
from unittest.mock import patch

from lean_merge import MergeError, merge, normalize


def setUpModule():
    environment = patch.dict(os.environ, {"LEAN_TOOL_FAILURE_ARCHIVE": "0"})
    environment.start()
    unittest.addModuleCleanup(environment.stop)


class SourceOrderTests(unittest.TestCase):
    def test_lifted_dependency_preserves_open_namespace(self):
        namespace = "namespace N\ndef f : Nat := 1\nend N\n"
        sibling = "theorem sibling : f = f := rfl\n"
        base = (namespace + "open N\ndef g := f\n"
                "theorem target : g = g := sorry\n" + sibling)
        donor = namespace + "def g := N.f\ntheorem target : g = g := rfl\n"
        for newline in ("\n", "\r\n"):
            with self.subTest(newline=newline):
                result = merge(base.replace("\n", newline), donor,
                               target="target", proof="target")
                self.assertTrue(result["verified"])
                self.assertIn(sibling.replace("\n", newline), result["content"])
                self.assertEqual(result["content"].count("def g := f"), 1)

    def test_lifted_dependency_preserves_section_parameters(self):
        result = merge(
            "universe u\nsection\nvariable {A : Type u} (a : A)\ninclude a\n"
            "theorem helper : True := True.intro\n"
            "theorem target : True := sorry\n"
            "theorem sibling : True := True.intro\nend\n",
            "universe v\ntheorem helper {A : Type v} (a : A) : True := True.intro\n"
            "theorem target {A : Type v} (a : A) : True := helper a\n",
            target="target", proof="target")
        self.assertTrue(result["verified"])
        self.assertIn("helper", result["reused"])

    def test_reordered_simp_cache_preserves_completed_theorem(self):
        # The new proof caches 1 = 1 first, so sibling._simp_1 changes to 2 = 2.
        sibling = "theorem sibling : 2 = 2 := by simp only [pair]\n"
        result = merge(
            "theorem pair : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩\n"
            "theorem target : 1 = 1 := sorry\n" + sibling,
            "theorem seed : (1 = 1) ∧ (3 = 3) := ⟨rfl, rfl⟩\n"
            "theorem target : 1 = 1 := by simp only [seed]\n",
            target="target", proof="target")
        self.assertTrue(result["verified"])
        self.assertNotIn("sorryAx", result["axioms"])
        self.assertIn(sibling, result["content"])

    def test_explicit_internal_theorem_type_is_still_checked(self):
        with self.assertRaisesRegex(MergeError, "changed the type of sibling._simp_1"):
            merge(
                "theorem target : True := sorry\n"
                "theorem sibling._simp_1 (x : helper) : (helper : Type) = helper := rfl\n",
                "def helper : Type := Nat\n"
                "theorem target : True := (fun (_ : helper) => True.intro) (0 : Nat)\n",
                target="target", proof="target")

    def test_preserves_tactic_only_dependency_and_comments(self):
        helper = "def identity (n : Nat) := n"
        proof = "theorem target (n : Nat) : n = n := by\n  -- keep this tactic\n  change identity n = n\n  rfl"
        result = merge("theorem target (n : Nat) : n = n := sorry\n",
                       helper + "\n\n" + proof + "\n", proof="target")
        self.assertIn(helper, result["source"])
        self.assertIn(proof, result["source"])
        self.assertEqual(result["strategy"], "source")
        self.assertNotIn("LeanMergeAux", result["source"])

    def test_normalize_preserves_notation_and_proof_text(self):
        proof = 'theorem target (n : Nat) : n = n := by change identity n = n; rfl'
        source = ('namespace N\nsection\nlocal notation "identity" => (fun n : Nat => n)\n'
                  + proof + '\nend\nend N\n')
        result = normalize(source, target="N.target")
        self.assertIn(proof, result["content"])
        self.assertIn('local notation "identity"', result["content"])
        self.assertIn("namespace N", result["content"])

    def test_conflict_does_not_fall_back_to_expansion(self):
        with self.assertRaisesRegex(MergeError, "Source name conflict"):
            merge("def f : Nat := 1\ntheorem target : 2 = 2 := sorry\n",
                  "def f : Nat := 2\ntheorem target : 2 = 2 := Eq.refl f\n",
                  target="target", proof="target")

    def test_normalize_private_type_after_removing_unused_private_declaration(self):
        source = ("private def unused : Nat := 1\nprivate opaque T : Type := Nat\n"
                  "theorem target (x : T) : x = x := by rfl\n")
        result = normalize(source, target="target")
        self.assertNotIn("unused", result["content"])
        self.assertIn("private opaque T : Type := Nat", result["content"])
        self.assertIn("theorem target (x : T) : x = x := by rfl", result["content"])
