set -o pipefail && make mlton && cat examples/suite.txt | xargs -I {} ./main examples/{}
