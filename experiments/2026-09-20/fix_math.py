from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'outputs'/'kobon-extension'/'manuscript.md'
s=p.read_text(encoding='utf8')
s=s.replace('of the extension programme initiated in Zarzuelo\'s March 2026 manuscript',
            'of Zarzuelo\'s March 2026 extension proposal')
s=s.replace('Let (B'+chr(92)+'subset'+chr(92)+'mathbb Z/(2n)'+chr(92)+') contain',
            'Let $B'+chr(92)+'subset'+chr(92)+'mathbb Z/(2n)$ contain')
out=[];in_block=False;found=set()
for line in s.splitlines():
    if line.strip()==chr(92)+'[':in_block=True
    if not in_block:
        i=0;parts=[]
        while i<len(line):
            if line[i]!='(' or i and line[i-1]==']':
                parts.append(line[i]);i+=1;continue
            j=i+1;depth=1
            while j<len(line) and depth:
                if line[j]=='(':depth+=1
                elif line[j]==')':depth-=1
                j+=1
            if depth:parts.append(line[i]);i+=1;continue
            raw=line[i+1:j-1]
            stripped=re.sub(r'\\[A-Za-z]+','',raw)
            is_math=not raw.isdigit() and not re.search(r'[A-Za-z]{2,}',stripped) and not raw.startswith('http')
            if is_math:parts.extend(['$',raw,'$']);found.add(raw)
            else:parts.append(line[i:j])
            i=j
        line=''.join(parts)
    out.append(line)
    if line.strip()==chr(92)+']':in_block=False
p.write_text('\n'.join(out)+'\n',encoding='utf8')
print('Converted',len(found),'distinct inline expressions:',sorted(found))
