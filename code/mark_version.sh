echo "**Version**: \`$(git rev-parse --verify --short HEAD)\`" >  tmp
echo "**Date**: \`$(date)\`"                                   >  tmp
echo ""                                                        >> tmp
cat $1 >> tmp
mv tmp $1
