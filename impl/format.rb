while gets
  puts $_.gsub(/(.*\.sml):(.*)-(.*) (Error|Warning):/, "\\4: \\1 \\2.\n")
end
