while gets
  puts $_.gsub(/(.*\.sml):(\d*\.\d*)(-(\d*\.\d*))? (Error|Warning):/, "\\5: \\1 \\2.\n")
end
