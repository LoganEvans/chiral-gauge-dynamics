-- FILENAME: Main.lean

import CGD
import Litlib.Core.CLI

def main (args : List String) : IO UInt32 :=
  Litlib.Core.CLI.runCli `CGD args
