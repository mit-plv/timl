set -o pipefail && make -C .. mlton && ../main --annoless annoless/stdlib.pkg annoless/test-suite.pkg && ../main stdlib.pkg test-suite.pkg
