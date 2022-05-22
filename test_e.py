#!/usr/bin/python3
import unittest
import sys
import tester
from gradescope_utils.autograder_utils.decorators import weight

if len(sys.argv) == 1:
  valgrind = True
else:
  valgrind = False

# sys.exit(tester.runIt("test-files-m", valgrind))

class Tests(unittest.TestCase):
  @weight(1)
  def testCode(self):
    return_value = tester.runIt("test-files-e", valgrind)
    if return_value != "":
        self.fail(return_value)
