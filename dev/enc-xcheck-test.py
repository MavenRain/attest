#!/usr/bin/env python3
"""Regressions for ELF layout validation and explicit, non-destructive pinning."""
import importlib.util
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location("enc_xcheck", ROOT / "dev/enc-xcheck.py")
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class HaltChecks(unittest.TestCase):
    def setUp(self):
        self.image = (ROOT / "corpus/halt.elf").read_bytes()
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.logs = Path(self.scratch.name)
        self.fixture = self.logs / "pinned.elf"
        self.fixture.write_bytes(self.image)
        self.patched = patch.object(GATE, "HALT", self.fixture)
        self.patched.start()
        self.addCleanup(self.patched.stop)

    def check(self, image, pin=False):
        return GATE.check_halt(image, pin, self.logs)

    def test_pinned_segment_alignment(self):
        _, _, offset, vaddr, _, _, _, align = struct.unpack_from("<IIQQQQQQ", self.image, 64)
        self.assertEqual(offset % align, vaddr % align)

    def test_valid_fixture(self):
        self.assertNotIn("FAIL", self.check(self.image))

    def test_missing_fixture_requires_pin(self):
        self.fixture.unlink()
        self.assertIn("FAIL", self.check(self.image))
        self.assertFalse(self.fixture.exists())

    def test_explicit_pin_creates_fixture(self):
        self.fixture.unlink()
        self.assertNotIn("FAIL", self.check(self.image, pin=True))
        self.assertEqual(self.fixture.read_bytes(), self.image)

    def test_invalid_pin_preserves_fixture(self):
        broken = bytearray(self.image)
        struct.pack_into("<Q", broken, 24, GATE.ENTRY + 4)
        self.assertIn("FAIL", self.check(bytes(broken), pin=True))
        self.assertEqual(self.fixture.read_bytes(), self.image)

    def test_pin_rejects_bad_segments(self):
        for offset, value in ((72, 120), (80, GATE.ENTRY + 4), (88, GATE.ENTRY + 4),
                              (96, 0), (104, 0), (112, 3)):
            with self.subTest(offset=offset):
                broken = bytearray(self.image)
                struct.pack_into("<Q", broken, offset, value)
                self.assertIn("FAIL", self.check(bytes(broken), pin=True))
                self.assertEqual(self.fixture.read_bytes(), self.image)

    def test_pin_rejects_wrong_halt_code(self):
        broken = bytearray(self.image)
        broken[-1] = 1
        self.assertIn("FAIL", self.check(bytes(broken), pin=True))
        self.assertEqual(self.fixture.read_bytes(), self.image)


if __name__ == "__main__":
    unittest.main()
