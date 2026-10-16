"""Comment/string-aware scanner for ordinary line-start named Lean declarations.
This is a source reconciliation aid, not a replacement for Lean's parser/kernel.
Nested comments, line comments, strings and binder-local := are handled explicitly.
"""
import re

def masked(text):
 out=list(text);i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):out[i:i+2]=[' ',' '];depth+=1;i+=2;continue
   if text.startswith('-/',i):out[i:i+2]=[' ',' '];depth-=1;i+=2;continue
   if text[i]!='\n':out[i]=' '
   i+=1;continue
  if string:
   if text[i]=='\\':
    out[i]=' ';i+=1
    if i<len(text):out[i]=' ';i+=1
    continue
   if text[i]=='"':string=False
   if text[i]!='\n':out[i]=' '
   i+=1;continue
  if text.startswith('/-',i):out[i:i+2]=[' ',' '];depth=1;i+=2;continue
  if text.startswith('--',i):
   while i<len(text) and text[i]!='\n':out[i]=' ';i+=1
   continue
  if text[i]=='"':out[i]=' ';string=True
  i+=1
 if depth or string:raise ValueError('Unclosed comment or string')
 return ''.join(out)

def declarations(text):
 code=masked(text);result={}
 pattern=r"(?m)^\s*(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def)\s+([A-Za-z_][\w'.]*)(?=\s|[:({\[])"
 for m in re.finditer(pattern,code):
  depth=0;i=m.end()
  while i<len(code):
   c=code[i]
   if c in '([{⦃':depth+=1
   elif c in ')]}⦄':depth-=1
   if depth==0 and code.startswith(':=',i):break
   if depth==0 and m.group(1)=='def' and c=='|' and not code[code.rfind('\n',0,i)+1:i].strip():break
   i+=1
  if i==len(code):raise ValueError('No declaration body for '+m.group(2))
  if m.group(2) in result:raise ValueError('Duplicate ordinary declaration name')
  result[m.group(2)]=dict(kind=m.group(1),header=text[m.end():i],start=m.start(),body_start=i+2 if code.startswith(':=',i) else i)
 return result

def self_test():
 sample='''/- theorem or /- theorem fake : False := nope -/ -/
-- theorem fake2 : False := nope
#check "theorem fake3 : False := nope"
theorem real (n : Nat := 0) : n = n := rfl
@[simp] theorem another : True := True.intro
'''
 d=declarations(sample);assert set(d)=={'real','another'} and '(n : Nat := 0)' in d['real']['header']
 self_test_nested=masked('/- outer /- inner -/ theorem bogus -/\ndef x := "-- /-"')
 assert 'bogus' not in self_test_nested
 assert set(declarations("def recur' : Nat → Nat\n | 0 => 0\n | k+1 => k\n"))=={"recur'"}

if __name__=='__main__':self_test();print('PASS: nested/line comments, strings, attributes, binder-local assignments and equation-style definitions')
