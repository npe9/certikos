# -*- coding: utf-8 -*-
#####################################################################
#                                                                   #
#          Script to generate the Template files for mCertiKOS      #
#                                                                   #
#           Author: Ronghui Gu                                      #
#           Email: ronghui.gu@yale.edu                              #
#                                                                   #
#                                                                   #
#####################################################################

# use Open3 to execute the shell command
require "open3"
require "set"

include Open3

def time_gen

  print "# Generate the timelog_t "

  filetime = ""
  filehash = {}

  File.foreach('./timelog_t') {|input|
    
    time = input[/(\S+)/,1]
    file = input[/\S+\s+(\S+)/,1]

    filehash [file] = time
  }

  File.foreach('../timelog') {|input|
    
    input = input[/\S+\s+real\s+\S+/]
    unless input == nil
      file = input[/(\S+)/,1]
      time = input[/real\s+(\S+)/,1]
      filehash [file] = time
    end
  }
  
  Hash[filehash.sort_by {|k,v| v.to_i}.reverse].each { |key, value|
    filetime << value + "\t" + key + "\n"
  }

  File.write('./timelog_t', filetime)
  File.write('../timelog', "")

  print "Finished!\n"

end
 
def ident_gen 
  
  print "# Generating GlobIdent.v..."

  ident_set = Set.new

  count = 1000
  config = "(* WARNING: This file is generated by #{$PROGRAM_NAME}.\n" +
           "            All modification will be lost when regenerating,\n" +
           "            modify script/ident_config instead. *)\n\n" +
           "Require Import Coqlib.\n\n" +
           "Open Local Scope positive.\n\n"

  File.foreach('./ident_config') {|input|
    
    ident = input.gsub(/#.*/," ")[/(\w+)/,1]
    
    unless ident == nil
      unless ident_set.include? ident
        config << "Let " + ident + " := " + count.to_s + ".\n"
        count = count + 10
        ident_set.add ident
      end
    end

  }

  File.write('../layerlib/GlobIdent.v', config)

  print " done.\n"

end

def symbols_gen

  print "# Generating Symbols.v... "

  f = File.new('../driver/Symbols.v', 'w')
  f.write("(* WARNING: This file is generated by #{$PROGRAM_NAME}.\n" +
          "            All modification will be lost when regenerating,\n" +
          "            modify script/ident_config instead. *)\n")
  ident_set = SortedSet.new

  File.foreach('./ident_config') {|input|

    ident = input.gsub(/#.*/," ")[/(\w+)/,1]

    unless ident == nil
      ident_set.add ident
    end

  }

  f.write(
    "Require Import String.\n" +
    "Require Import compcert.lib.Coqlib.\n" +
    "Require Import compcert.common.AST.\n" +
    "Require Import compcertx.backend.I64helpers.\n" +
    "Require Import liblayers.compcertx.ErrorMonad.\n" +
    "Require Import mcertikos.layerlib.GlobIdent.\n\n" +

    "Fixpoint reserved_symbols_aux (accu: list (ident * string)) (l: list string): res (list (ident * string)) :=\n" +
    "  match l with\n" +
    "    | nil => ret accu\n" +
    "    | (s :: l') =>\n" +
    "      i <- reserved_id s;\n" +
    "      reserved_symbols_aux ((i, s) :: accu) l'\n" +
    "  end.\n\n" +

    "Definition reserved_symbols_strong :\n" +
    "  {l | reserved_symbols_aux nil reserved_strings = ret l}.\n" +
    "Proof.\n" +
    "  vm_compute. eauto.\n" +
    "Defined.\n\n" +

    "Definition reserved_symbols :=\n" +
    "  let (l, _) := reserved_symbols_strong in l.\n\n" +

    "Open Scope string_scope.\n\n" +

    "Definition symbols: list (ident * string) :=\n")

  ident_set.each { |ident|
    f.write("  (#{ident}, \"#{ident}\") ::\n")
  }

  f.write("  reserved_symbols.\n")
  f.close()

  print " done.\n"

end

def abs_gen 
  
  print "# Generate the AbstractDataType_TEMP.v "

  ident_set = Set.new

  config = "(* Generated by Ruby Script *)\n\n"

  File.foreach('./abs_config') {|input|
    
    ident = input.gsub(/#.*/," ")[/(\w+)\W*:/,1]
    
    unless ident == nil
      ident_set.add ident
    end
  }

  update = ""
  notation = ""
  instance = ""

  ident_a = ident_set.to_a

  ident_a.each { |ident|
    
    update << "Definition update_" + ident + " (a : RData) b := \n mkRData"
    ident_a.each_with_index { |id, i|
      if id == ident then
        update << " b"
      else
        update << " (" + id + " a)"
      end

      if i >= 9 && i % 9 == 0
        update << "\n"
      end
    }
    update << ".\n\n"
    notation << "Notation \"a {"+ ident + " : b }\" := (update_" + ident +" a b) (at level 1).\n"
    
    instance << "Section CLASS_" + ident +".\n\n"
    instance << "Class relate_impl_" + ident + " :=\n"
    instance << "{\nrelate_impl_" + ident + "_eq s ι d1 d2:\n"
    instance << "relate_AbData s ι d1 d2 ->\n"
    instance << ident + " d1 = " + ident + " d2;\n\n"
    instance << "relate_impl_" + ident +"_update s ι d1 d2:\n"
    instance << "relate_AbData s ι d1 d2 ->\n"
    instance << "forall b, relate_AbData s ι d1 {" + ident + ": b} d2 {" + ident + ": b}\n}.\n\n"
    instance << " Class match_impl_" + ident + " :=\n"
    instance << "{\n match_impl_" + ident +"_update ι d m f:\n"
    instance << "match_AbData ι d m f ->\n"
    instance << "forall b, match_AbData ι d {" + ident + ": b} m f\n}.\n\n"
    instance << "End CLASS_" + ident + ".\n\n"

  }

  File.write('./AbstractDataType_TEMP.v', update << "\n\n" + notation << "\n\n" + instance)

  print "Finished!\n"

end

def help
  
  print "# This script can generate some templates for mCertiKOS\n"
  print "# The legal arguments are as below:\n"
  print "# help : print the help information\n"
  print "# ident : generate GlobIdent.v file from the configurarion file globalident_config\n"
  print "# abs : generate AbstractDataType_TEMP.v file from the configurarion file abs_config\n"
  print "# time : generate the time analysis for each file from timelog\n"
  print "# symbols : generate the symobls for code extraction\n"

end

if ARGV.empty?
  help
end

ARGV.each { |arg|
  case arg
  when "help"
    help
  when "ident"
    ident_gen
  when "symbols"
    symbols_gen
  when "abs"
    abs_gen
  when "time"
    time_gen
  else
    print "# \"" + arg + "\" is not acceptable\n"
    help
  end
}
