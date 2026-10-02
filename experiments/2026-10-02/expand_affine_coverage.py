"""Match exact positive-dependency subsystems against all236 affine types.

The18 P-classes classify22-support closures including infinity. The236 E-class
words, not merely18 chosen deletions, are the complete affine input. For each
affine type every possible distinguished support is tested in its affine order.
Certified subsystems are reused under row-sign reversal and grid reflection.
"""
from verify_grid_obstruction import *

TRIPLES=list(itertools.combinations(range(20),3));INDEX={t:i for i,t in enumerate(TRIPLES)}


def transformed_support(support,reflect,sign):
    out=[]
    for row in support:
        if row[0]=='triple':
            _,i,j,k,s=row
            out.append(['triple',19-k,19-j,19-i,s*sign]if reflect else ['triple',i,j,k,s*sign])
        else:
            _,i,j,s=row
            out.append(['cap',19-j,19-i,-s*sign]if reflect else ['cap',i,j,s*sign])
    return out


def masks(support):
    pos=0;mask=0
    for row in support:
        idx=INDEX[tuple(row[1:4])]if row[0]=='triple'else len(TRIPLES)+row[1]
        bit=1<<idx
        assert not(mask&bit),'A support repeats a signed constraint'
        mask|=bit
        if row[-1]>0:pos|=bit
    return mask,pos


def triangle_count(raw):
    word=[int(s)for s in raw.split(')',1)[1].split()];perm=list(range(21));rows=[[]for _ in perm]
    for g in word:
        i,j=perm[g:g+2];rows[i].append(j);rows[j].append(i);perm[g],perm[g+1]=j,i
    counts={}
    for i,row in enumerate(rows):
        for j,k in zip(row,row[1:]):
            t=tuple(sorted((i,j,k)));counts[t]=counts.get(t,0)+1
    return sum(v==3 for v in counts.values())


def main(certificate,words,out):
    started=time.time();data=json.loads(certificate.read_text());raw=[s for s in words.read_text().splitlines()if ')'in s]
    assert len(raw)==236;assert all(triangle_count(s)==133 for s in raw)
    patterns=[]
    for rec in data['records']:
        if rec['status']!='exact_symbolic_positive_dependency':continue
        for reflection,sign in itertools.product((False,True),(1,-1)):
            sup=transformed_support(rec['support'],reflection,sign);mask,pos=masks(sup)
            patterns.append((mask,pos,rec['case_index'],reflection,sign))
    patterns.sort(key=lambda p:p[0].bit_count());records=[];distinct={};covered=0
    for ci,text in enumerate(raw):
        chi=decode_word(text)
        for I in range(21):
            signs,caps=chart(chi,I,0);assert caps is not None
            values=list(signs.values())+caps;bits=sum(1<<i for i,s in enumerate(values)if s>0)
            match=None
            for mask,pos,case,refl,sg in patterns:
                if bits&mask==pos:match=dict(certificate=case,reflection=refl,sign=sg);break
            row=dict(class_index=ci,I=I,covered=match is not None)
            if match is not None:row.update(match);covered+=1
            records.append(row);distinct.setdefault(bits,row)
    missing=[row for row in distinct.values()if not row['covered']]
    result=dict(source=str(words),word_sha256=hashlib.sha256(words.read_bytes()).hexdigest(),
       certificate_sha256=hashlib.sha256(certificate.read_bytes()).hexdigest(),
       affine_classes=236,all_word_triangle_counts=133,normalizations=len(records),covered_occurrences=covered,
       distinct_systems=len(distinct),uncovered_distinct=missing,records=records,seconds=time.time()-started,
       status='Subsystem matching only; used transformed certificates require independent exact verification')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('records','uncovered_distinct')}|{'uncovered_count':len(missing)}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('words',type=Path);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();main(a.certificate,a.words,a.out)
