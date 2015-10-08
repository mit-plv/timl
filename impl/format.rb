#! /usr/bin/env ruby

while gets
  puts $_.gsub(/([^ ]*):(\d*\.\d*)(-(\d*\.\d*))? (Error|Warning):/, "\\5: \\1 \\2.\n")
end
