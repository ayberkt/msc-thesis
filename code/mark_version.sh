echo "-- Version: $(git rev-parse --verify --short HEAD)\n" >> tmp
cat $1 >> tmp
mv tmp $1
