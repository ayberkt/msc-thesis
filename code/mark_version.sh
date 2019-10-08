echo "-- Version: $(git rev-parse --verify --short HEAD)" >  tmp
echo ""                                                   >> tmp
cat $1 >> tmp
mv tmp $1
