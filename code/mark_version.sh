echo "\`\`\`\nVersion: \`$(git rev-parse --verify --short HEAD)\`\n\`\`\`" >  tmp
echo ""                                                   >> tmp
cat $1 >> tmp
mv tmp $1
