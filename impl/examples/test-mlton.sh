set -o pipefail && make -C .. mlton && ../main stdlib.pkg suite.pkg
