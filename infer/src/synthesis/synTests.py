import sys
import unittest
import re
import subprocess

class SynthTestsSimple(unittest.TestCase):
  path_to_infer = "infer"

  def setUp(self):
    result_file = open("/tmp/result.c", "w+")
    result_file.write("")
    result_file.close()

  def test_swap(self):
    path_to_infer = self.path_to_infer
    spec_file_path = "/tmp/syn_read_test_spec.txt"
    spec_file = open(spec_file_path, "w+")
    spec_str = "[; x |-> a * y |-> b] void swap (int* x, int* y) [; x |-> b * y |-> a]"
    spec_file.write(spec_str)
    spec_file.close()
    subprocess.run([path_to_infer, "synthesize", "--synth-path", spec_file_path], 
      stdout=subprocess.PIPE)

    result_file = open("/tmp/result.c", "r")
    result = result_file.read()
    result_file.close()
    desired_result = \
      "#include <stdio.h>" + \
      "void swap(int* x, int* y) {" + \
        "int n$6 = *x;" + \
        "int n$9 = *y;" + \
        "*x = n$9;" + \
        "*y = n$6;" + \
      "}" + \
      "int main() { return 0; }"
    trim_result = re.sub(r'\s', '', result)
    trim_d_result = re.sub(r'\s', '', desired_result)
    self.assertEqual(trim_result, trim_d_result)

  def test_const_write(self):
    path_to_infer = self.path_to_infer
    spec_file_path = "/tmp/syn_write_const_spec.txt"
    spec_file = open(spec_file_path, "w+")
    spec_str = "[; x |-> a] void forty_two (int* x) [; x |-> 42]"
    spec_file.write(spec_str)
    spec_file.close()
    subprocess.run([path_to_infer, "synthesize", "--synth-path", spec_file_path], 
      stdout=subprocess.PIPE)

    result_file = open("/tmp/result.c", "r")
    result = result_file.read()
    result_file.close()
    desired_result = \
      "#include <stdio.h> " + \
      "void forty_two (int* x) { " + \
        "int n$1 = *x; " + \
        "*x = 42; " + \
      "} " + \
      "int main() { return 0; }"
    trim_result = re.sub(r'\s', '', result)
    trim_d_result = re.sub(r'\s', '', desired_result)
    self.assertEqual(trim_result, trim_d_result)


if __name__ == "__main__":
  if len(sys.argv) != 2: 
    sys.exit("Usage: python synTests.py path/to/infer")
  
  SynthTestsSimple.path_to_infer = sys.argv.pop()
  unittest.main()