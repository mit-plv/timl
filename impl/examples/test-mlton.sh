set -o pipefail && make -C .. mlton && ../main stdlib.pkg test-suite.pkg
