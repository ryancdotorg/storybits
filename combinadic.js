(function(exports){
  // A somewhat stripped down version of Leemon Baird's BigInt.js

  ///////////////////////////////////
  //                               //
  //  BEGIN BIGINT IMPLEMENTATION  //
  //                               //
  ///////////////////////////////////

  bpe=0;         //bits stored per array element
  mask=0;        //AND this with an array element to chop it down to bpe bits
  radix=mask+1;  //equals 2^bpe.  A single 1 bit to the left of the last bit of mask.

  //the digits for converting to different bases
  digitsStr='0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_=!@#$%^&*()[]{}|;:,.<>/?`~ \\\'\"+-';

  //initialize the global variables
  for (bpe=0; (1<<(bpe+1)) > (1<<bpe); bpe++) {};  //bpe=number of bits in the mantissa on this platform
  bpe>>=1;                   //bpe=number of bits in one element of the array representing the bigInt
  mask=(1<<bpe)-1;           //AND the mask with an integer to get its bpe least significant bits
  radix=mask+1;              //2^bpe.  a single 1 bit to the left of the first bit of mask

  //the following global variables are scratchpad memory to 
  //reduce dynamic memory allocation in the inner loop
  t=new Array(0);
  ss=t;       //used in mult_()
  s4=t; s5=t; //used in mod_()
  s6=t;       //used in bigInt2str()
  md_q1=t; md_q2=t; md_q3=t; md_r=t; md_r1=t; md_r2=t; md_tt=t; //used in mod_()

  ////////////////////////////////////////////////////////////////////////////////////////

  //returns how many bits long the bigInt is, not counting leading zeros.
  function bitSize(x) {
    var j,z,w;
    for (j=x.length-1; (x[j]==0) && (j>0); j--) {};
    for (z=0,w=x[j]; w; (w>>=1),z++) {};
    z+=bpe*j;
    return z;
  }

  //return a copy of x with at least n elements, adding leading zeros if needed
  function expand(x,n) {
    var ans=int2bigInt(0,(x.length>n ? x.length : n)*bpe,0);
    copy_(ans,x);
    return ans;
  }

  //return a new bigInt equal to (x mod n) for bigInts x and n.
  function mod(x,n) {
    var ans=dup(x);
    mod_(ans,n);
    return trim(ans,1);
  }

  //return (x+n) where x is a bigInt and n is an integer.
  function addInt(x,n) {
    var ans=expand(x,x.length+1);
    addInt_(ans,n);
    return trim(ans,1);
  }

  //return x*y for bigInts x and y. This is faster when y<x.
  function mult(x,y) {
    var ans=expand(x,x.length+y.length);
    mult_(ans,y);
    return trim(ans,1);
  }

  //return (x-y) for bigInts x and y.  Negative answers will be 2s complement
  function sub(x,y) {
    var ans=expand(x,(x.length>y.length ? x.length+1 : y.length+1)); 
    sub_(ans,y);
    return trim(ans,1);
  }

  //return (x+y) for bigInts x and y.  
  function add(x,y) {
    var ans=expand(x,(x.length>y.length ? x.length+1 : y.length+1)); 
    add_(ans,y);
    return trim(ans,1);
  }

  //return (x*y mod n) for bigInts x,y,n.  For greater speed, let y<x.
  function multMod(x,y,n) {
    var ans=expand(x,n.length);
    multMod_(ans,y,n);
    return trim(ans,1);
  }

  //is bigInt x negative?
  function negative(x) {
    return ((x[x.length-1]>>(bpe-1))&1);
  }


  //is (x << (shift*bpe)) > y?
  //x and y are nonnegative bigInts
  //shift is a nonnegative integer
  function greaterShift(x,y,shift) {
    var i, kx=x.length, ky=y.length;
    k=((kx+shift)<ky) ? (kx+shift) : ky;
    for (i=ky-1-shift; i<kx && i>=0; i++) 
      if (x[i]>0)
        return 1; //if there are nonzeros in x to the left of the first column of y, then x is bigger
    for (i=kx-1+shift; i<ky; i++)
      if (y[i]>0)
        return 0; //if there are nonzeros in y to the left of the first column of x, then x is not bigger
    for (i=k-1; i>=shift; i--)
      if      (x[i-shift]>y[i]) return 1;
      else if (x[i-shift]<y[i]) return 0;
    return 0;
  }

  //is x > y? (x and y both nonnegative)
  function greater(x,y) {
    var i;
    var k=(x.length<y.length) ? x.length : y.length;

    for (i=x.length;i<y.length;i++)
      if (y[i])
        return 0;  //y has more digits

    for (i=y.length;i<x.length;i++)
      if (x[i])
        return 1;  //x has more digits

    for (i=k-1;i>=0;i--)
      if (x[i]>y[i])
        return 1;
      else if (x[i]<y[i])
        return 0;
    return 0;
  }

  //divide x by y giving quotient q and remainder r.  (q=floor(x/y),  r=x mod y).  All 4 are bigints.
  //x must have at least one leading zero element.
  //y must be nonzero.
  //q and r must be arrays that are exactly the same length as x. (Or q can have more).
  //Must have x.length >= y.length >= 2.
  function divide_(x,y,q,r) {
    var kx, ky;
    var i,j,y1,y2,c,a,b;
    copy_(r,x);
    for (ky=y.length;y[ky-1]==0;ky--) {}; //ky is number of elements in y, not including leading zeros

    //normalize: ensure the most significant element of y has its highest bit set  
    b=y[ky-1];
    for (a=0; b; a++)
      b>>=1;  
    a=bpe-a;  //a is how many bits to shift so that the high order bit of y is leftmost in its array element
    leftShift_(y,a);  //multiply both by 1<<a now, then divide both by that at the end
    leftShift_(r,a);

    //Rob Visser discovered a bug: the following line was originally just before the normalization.
    for (kx=r.length;r[kx-1]==0 && kx>ky;kx--) {}; //kx is number of elements in normalized x, not including leading zeros

    copyInt_(q,0);                      // q=0
    while (!greaterShift(y,r,kx-ky)) {  // while (leftShift_(y,kx-ky) <= r) {
      subShift_(r,y,kx-ky);             //   r=r-leftShift_(y,kx-ky)
      q[kx-ky]++;                       //   q[kx-ky]++;
    }                                   // }

    for (i=kx-1; i>=ky; i--) {
      if (r[i]==y[ky-1])
        q[i-ky]=mask;
      else
        q[i-ky]=Math.floor((r[i]*radix+r[i-1])/y[ky-1]);	

      //The following for(;;) loop is equivalent to the commented while loop, 
      //except that the uncommented version avoids overflow.
      //The commented loop comes from HAC, which assumes r[-1]==y[-1]==0
      //  while (q[i-ky]*(y[ky-1]*radix+y[ky-2]) > r[i]*radix*radix+r[i-1]*radix+r[i-2])
      //    q[i-ky]--;    
      for (;;) {
        y2=(ky>1 ? y[ky-2] : 0)*q[i-ky];
        c=y2>>bpe;
        y2=y2 & mask;
        y1=c+q[i-ky]*y[ky-1];
        c=y1>>bpe;
        y1=y1 & mask;

        if (c==r[i] ? y1==r[i-1] ? y2>(i>1 ? r[i-2] : 0) : y1>r[i-1] : c>r[i]) 
          q[i-ky]--;
        else
          break;
      }

      linCombShift_(r,y,-q[i-ky],i-ky);    //r=r-q[i-ky]*leftShift_(y,i-ky)
      if (negative(r)) {
        addShift_(r,y,i-ky);         //r=r+leftShift_(y,i-ky)
        q[i-ky]--;
      }
    }

    rightShift_(y,a);  //undo the normalization step
    rightShift_(r,a);  //undo the normalization step
  }

  //do carries and borrows so each element of the bigInt x fits in bpe bits.
  function carry_(x) {
    var i,k,c,b;
    k=x.length;
    c=0;
    for (i=0;i<k;i++) {
      c+=x[i];
      b=0;
      if (c<0) {
        b=-(c>>bpe);
        c+=b*radix;
      }
      x[i]=c & mask;
      c=(c>>bpe)-b;
    }
  }

  //return x mod n for bigInt x and integer n.
  function modInt(x,n) {
    var i,c=0;
    for (i=x.length-1; i>=0; i--)
      c=(c*radix+x[i])%n;
    return c;
  }

  //convert the integer t into a bigInt with at least the given number of bits.
  //the returned array stores the bigInt in bpe-bit chunks, little endian (buff[0] is least significant word)
  //Pad the array with leading zeros so that it has at least minSize elements.
  //There will always be at least one leading 0 element.
  function int2bigInt(t,bits,minSize) {   
    var i,k;
    k=Math.ceil(bits/bpe)+1;
    k=minSize>k ? minSize : k;
    buff=new Array(k);
    copyInt_(buff,t);
    return buff;
  }

  //return the bigInt given a string representation in a given base.  
  //Pad the array with leading zeros so that it has at least minSize elements.
  //If base=-1, then it reads in a space-separated list of array elements in decimal.
  //The array will always have at least one leading zero, unless base=-1.
  function str2bigInt(s,base,minSize) {
    var d, i, j, x, y, kk;
    var k=s.length;
    if (base==-1) { //comma-separated list of array elements in decimal
      x=new Array(0);
      for (;;) {
        y=new Array(x.length+1);
        for (i=0;i<x.length;i++)
          y[i+1]=x[i];
        y[0]=parseInt(s,10);
        x=y;
        d=s.indexOf(',',0);
        if (d<1) 
          break;
        s=s.substring(d+1);
        if (s.length==0)
          break;
      }
      if (x.length<minSize) {
        y=new Array(minSize);
        copy_(y,x);
        return y;
      }
      return x;
    }

    x=int2bigInt(0,base*k,0);

    if (base<=36 && d>=36)  //convert uppercase to lowercase if base<=36
        s = s.toLowerCase();

    for (i=0;i<k;i++) {
      d=digitsStr.indexOf(s.substring(i,i+1),0);
      if (d>=base || d<0) {   //stop at first illegal character
        break;
      }
      multInt_(x,base);
      addInt_(x,d);
    }

    for (k=x.length;k>0 && !x[k-1];k--) {}; //strip off leading zeros
    k=minSize>k+1 ? minSize : k+1;
    y=new Array(k);
    kk=k<x.length ? k : x.length;
    for (i=0;i<kk;i++)
      y[i]=x[i];
    for (;i<k;i++)
      y[i]=0;
    return y;
  }

  //is bigint x equal to integer y?
  //y must have less than bpe bits
  function equalsInt(x,y) {
    var i;
    if (x[0]!=y)
      return 0;
    for (i=1;i<x.length;i++)
      if (x[i])
        return 0;
    return 1;
  }

  //are bigints x and y equal?
  //this works even if x and y are different lengths and have arbitrarily many leading zeros
  function equals(x,y) {
    var i;
    var k=x.length<y.length ? x.length : y.length;
    for (i=0;i<k;i++)
      if (x[i]!=y[i])
        return 0;
    if (x.length>y.length) {
      for (;i<x.length;i++)
        if (x[i])
          return 0;
    } else {
      for (;i<y.length;i++)
        if (y[i])
          return 0;
    }
    return 1;
  }

  //is the bigInt x equal to zero?
  function isZero(x) {
    var i;
    for (i=0;i<x.length;i++)
      if (x[i])
        return 0;
    return 1;
  }

  //convert a bigInt into a string in a given base, from base 2 up to base 95.
  //Base -1 prints the contents of the array representing the number.
  function bigInt2str(x,base) {
    var i,t,s="";

    if (s6.length!=x.length) 
      s6=dup(x);
    else
      copy_(s6,x);

    if (base==-1) { //return the list of array contents
      for (i=x.length-1;i>0;i--)
        s+=x[i]+',';
      s+=x[0];
    }
    else { //return it in the given base
      while (!isZero(s6)) {
        t=divInt_(s6,base);  //t=s6 % base; s6=floor(s6/base);
        s=digitsStr.substring(t,t+1)+s;
      }
    }
    if (s.length==0)
      s="0";
    return s;
  }

  //returns a duplicate of bigInt x
  function dup(x) {
    var i;
    buff=new Array(x.length);
    copy_(buff,x);
    return buff;
  }

  //do x=y on bigInts x and y.  x must be an array at least as big as y (not counting the leading zeros in y).
  function copy_(x,y) {
    var i;
    var k=x.length<y.length ? x.length : y.length;
    for (i=0;i<k;i++)
      x[i]=y[i];
    for (i=k;i<x.length;i++)
      x[i]=0;
  }

  //do x=y on bigInt x and integer y.  
  function copyInt_(x,n) {
    var i,c;
    for (c=n,i=0;i<x.length;i++) {
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do x=x+n where x is a bigInt and n is an integer.
  //x must be large enough to hold the result.
  function addInt_(x,n) {
    var i,k,c,b;
    x[0]+=n;
    k=x.length;
    c=0;
    for (i=0;i<k;i++) {
      c+=x[i];
      b=0;
      if (c<0) {
        b=-(c>>bpe);
        c+=b*radix;
      }
      x[i]=c & mask;
      c=(c>>bpe)-b;
      if (!c) return; //stop carrying as soon as the carry is zero
    }
  }

  //right shift bigInt x by n bits.  0 <= n < bpe.
  function rightShift_(x,n) {
    var i;
    var k=Math.floor(n/bpe);
    if (k) {
      for (i=0;i<x.length-k;i++) //right shift x by k elements
        x[i]=x[i+k];
      for (;i<x.length;i++)
        x[i]=0;
      n%=bpe;
    }
    for (i=0;i<x.length-1;i++) {
      x[i]=mask & ((x[i+1]<<(bpe-n)) | (x[i]>>n));
    }
    x[i]>>=n;
  }

  //do x=floor(|x|/2)*sgn(x) for bigInt x in 2's complement
  function halve_(x) {
    var i;
    for (i=0;i<x.length-1;i++) {
      x[i]=mask & ((x[i+1]<<(bpe-1)) | (x[i]>>1));
    }
    x[i]=(x[i]>>1) | (x[i] & (radix>>1));  //most significant bit stays the same
  }

  //left shift bigInt x by n bits.
  function leftShift_(x,n) {
    var i;
    var k=Math.floor(n/bpe);
    if (k) {
      for (i=x.length; i>=k; i--) //left shift x by k elements
        x[i]=x[i-k];
      for (;i>=0;i--)
        x[i]=0;  
      n%=bpe;
    }
    if (!n)
      return;
    for (i=x.length-1;i>0;i--) {
      x[i]=mask & ((x[i]<<n) | (x[i-1]>>(bpe-n)));
    }
    x[i]=mask & (x[i]<<n);
  }

  //do x=x*n where x is a bigInt and n is an integer.
  //x must be large enough to hold the result.
  function multInt_(x,n) {
    var i,k,c,b;
    if (!n)
      return;
    k=x.length;
    c=0;
    for (i=0;i<k;i++) {
      c+=x[i]*n;
      b=0;
      if (c<0) {
        b=-(c>>bpe);
        c+=b*radix;
      }
      x[i]=c & mask;
      c=(c>>bpe)-b;
    }
  }

  //do x=floor(x/n) for bigInt x and integer n, and return the remainder
  function divInt_(x,n) {
    var i,r=0,s;
    for (i=x.length-1;i>=0;i--) {
      s=r*radix+x[i];
      x[i]=Math.floor(s/n);
      r=s%n;
    }
    return r;
  }

  //do the linear combination x=a*x+b*y for bigInts x and y, and integers a and b.
  //x must be large enough to hold the answer.
  function linComb_(x,y,a,b) {
    var i,c,k,kk;
    k=x.length<y.length ? x.length : y.length;
    kk=x.length;
    for (c=0,i=0;i<k;i++) {
      c+=a*x[i]+b*y[i];
      x[i]=c & mask;
      c>>=bpe;
    }
    for (i=k;i<kk;i++) {
      c+=a*x[i];
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do the linear combination x=a*x+b*(y<<(ys*bpe)) for bigInts x and y, and integers a, b and ys.
  //x must be large enough to hold the answer.
  function linCombShift_(x,y,b,ys) {
    var i,c,k,kk;
    k=x.length<ys+y.length ? x.length : ys+y.length;
    kk=x.length;
    for (c=0,i=ys;i<k;i++) {
      c+=x[i]+b*y[i-ys];
      x[i]=c & mask;
      c>>=bpe;
    }
    for (i=k;c && i<kk;i++) {
      c+=x[i];
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do x=x+(y<<(ys*bpe)) for bigInts x and y, and integers a,b and ys.
  //x must be large enough to hold the answer.
  function addShift_(x,y,ys) {
    var i,c,k,kk;
    k=x.length<ys+y.length ? x.length : ys+y.length;
    kk=x.length;
    for (c=0,i=ys;i<k;i++) {
      c+=x[i]+y[i-ys];
      x[i]=c & mask;
      c>>=bpe;
    }
    for (i=k;c && i<kk;i++) {
      c+=x[i];
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do x=x-(y<<(ys*bpe)) for bigInts x and y, and integers a,b and ys.
  //x must be large enough to hold the answer.
  function subShift_(x,y,ys) {
    var i,c,k,kk;
    k=x.length<ys+y.length ? x.length : ys+y.length;
    kk=x.length;
    for (c=0,i=ys;i<k;i++) {
      c+=x[i]-y[i-ys];
      x[i]=c & mask;
      c>>=bpe;
    }
    for (i=k;c && i<kk;i++) {
      c+=x[i];
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do x=x-y for bigInts x and y.
  //x must be large enough to hold the answer.
  //negative answers will be 2s complement
  function sub_(x,y) {
    var i,c,k,kk;
    k=x.length<y.length ? x.length : y.length;
    for (c=0,i=0;i<k;i++) {
      c+=x[i]-y[i];
      x[i]=c & mask;
      c>>=bpe;
    }
    for (i=k;c && i<x.length;i++) {
      c+=x[i];
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do x=x+y for bigInts x and y.
  //x must be large enough to hold the answer.
  function add_(x,y) {
    var i,c,k,kk;
    k=x.length<y.length ? x.length : y.length;
    for (c=0,i=0;i<k;i++) {
      c+=x[i]+y[i];
      x[i]=c & mask;
      c>>=bpe;
    }
    for (i=k;c && i<x.length;i++) {
      c+=x[i];
      x[i]=c & mask;
      c>>=bpe;
    }
  }

  //do x=x*y for bigInts x and y.  This is faster when y<x.
  function mult_(x,y) {
    var i;
    if (ss.length!=2*x.length)
      ss=new Array(2*x.length);
    copyInt_(ss,0);
    for (i=0;i<y.length;i++)
      if (y[i])
        linCombShift_(ss,x,y[i],i);   //ss=1*ss+y[i]*(x<<(i*bpe))
    copy_(x,ss);
  }

  //do x=x mod n for bigInts x and n.
  function mod_(x,n) {
    if (s4.length!=x.length)
      s4=dup(x);
    else
      copy_(s4,x);
    if (s5.length!=x.length)
      s5=dup(x);  
    divide_(s4,n,s5,x);  //x = remainder of s4 / n
  }

  //return x with exactly k leading zero elements
  function trim(x,k) {
    var i,y;
    for (i=x.length; i>0 && !x[i-1]; i--) {};
    y=new Array(i+k);
    copy_(y,x);
    return y;
  }

  /////////////////////////////////
  //                             //
  //  END BIGINT IMPLEMENTATION  //
  //                             //
  /////////////////////////////////

  // Expects n and k as normal integers, returns a bigint object.
  // Should be fairly easy to adapt to any bigint implementation.
  function nCk(n, k, bits) {
    if (!bits) bits = 256;

    var m;
    var quotient = int2bigInt(0, bits);
    if (k > n) return quotient;
    var remainder = int2bigInt(0, bits*2);
    var numerator = int2bigInt(1, bits*2);
    var denominator = int2bigInt(1, bits*2);
    for (var i = 1; i <= k; i++) {
      m = n - (k - i);
      multInt_(numerator, m);
      multInt_(denominator, i);
    }
    // The numerator is not guaranteed to be a multiple of the denominator
    // until after the last iteration of the loop, so division happens here.
    divide_(numerator, denominator, quotient, remainder);
    return quotient;
  }

  function minValues(max_x, cardinality) {
    max_x = typeof max_x === 'number' ? int2bigInt(max_x, 53) : dup(max_x);
    var bits = bitSize(max_x);

    var c, n = 0;
    var max_n = cardinality >> 1;
    do {
      if (n >= max_n) return null;
      c = nCk(cardinality, ++n, bits);
    } while (greater(max_x, c));
    return n;
  }

  function findBestN(x, start_n, k) {
    var last, incr, n, c, start_n, best_n, best_c;
    last = incr = n = start_n;
    best_n = best_c = 0;

    while (last || incr) {
      last = incr;
      incr >>>= 1;
      c = nCk(n, k);
      if (!greater(c, x)) {
        if (n > best_n) {
          best_n = n;
          best_c = c;
        }
        n += incr + 1;
      } else {
        n -= incr + 1;
      }
    }
    return {n: best_n, c: best_c};
  }

  function int2cmb(x, cardinality, n_values) {
    x = typeof x === 'number' ? int2bigInt(x, 53) : dup(x);

    var best;
    var k = n_values || minValues(x, cardinality);
    var n = cardinality;
    var values = [];

    do {
      best = findBestN(x, n, k);
      n = best.n;
      values.push(n);
      sub_(x, best.c);
    } while (--k);

    return values;
  }

  function cmb2int(values, bits) {
    if (!bits) bits = 256;
    // get a sorted copy
    values = values.slice().sort(function(a,b){return a-b;});

    var c;
    var x = int2bigInt(0, bits);

    for (var _len = values.length, i = 0; i < _len; ++i) {
      c = nCk(values[i], i + 1, bits);
      add_(x, c);
    }
    return x;
  }

  exports['MultisetCodec'] = (function(sets) {
    var __MultisetCodec = function(sets) {
      if (this.constructor !== __MultisetCodec) throw new Error("missing 'new'");
      var self = this;
      self['sets'] = sets;

      function neededItems(max_x) {
        max_x = typeof max_x === 'number' ? int2bigInt(max_x, 53) : dup(max_x);
        var k = 1, accum, _len, i, c, n, bits = bitSize(max_x);

        while (1) {
          accum = int2bigInt(1, bits);
          for (_len = self['sets'].length, i = 0; i < _len; ++i) {
            n = self['sets'][i];
            c = nCk(n, k, bits);
            mult_(accum, c);
          }
          // (accum >= max_x) == !(max_x > accum)
          if (!(greater(max_x, accum))) {
            return k;
          }
          ++k;
        }
      }

      function encode(x, max_x) {
        x = typeof x === 'number' ? int2bigInt(x, 53) : dup(x);
        if (typeof max_x === 'undefined') {
          max_x = dup(x);
        } else if (typeof max_x === 'number') {
          max_x = int2bigInt(max_x, 53);
        } else {
          max_x = dup(max_x);
        }

        var bits = bitSize(max_x), cardinality, subcmb;
        var needed = neededItems(max_x), result = [], i, j, _len, k, base;
        var n = int2bigInt(0, bits), tmp = int2bigInt(0, bits);

        for (_len = self['sets'].length, i = 0; i < _len; ++i) {
          cardinality = self['sets'][i];
          k = needed;
          base = nCk(cardinality, k, bits);
          divide_(x, base, tmp, n);
          x = dup(tmp);
          subcmb = int2cmb(n, cardinality, k);
          for (j = 0; j < k; ++j) {
            result.push([i, subcmb[j]]);
          }
        }
        return result;
      }

      function decode(l, bits) {
        if (!bits) bits = 256;
        var sublists = {}, sublist, sublist_idx = [];
        var i, _len, n, v, x, k, c;

        for (_len = l.length, i = 0; i < _len; ++i) {
          s = l[i][0], v = l[i][1];
          sublists[s] = (sublists[s] || []);
          sublists[s].push(v);
        }

        for (s in sublists) sublists[s].sort(function(a,b){return a-b;});

        x = int2bigInt(0, bits);
        for (i = sets.length; i--;) {
          sublist = sublists[i];
          if (!sublist) throw new Error("incomplete data to decode");
          n = self['sets'][i];
          k = sublist.length;
          c = nCk(n, k, bits);
          //var log = bigInt2str(x, 10) + ' ' + bigInt2str(c, 10)
          mult_(x, c);
          v = cmb2int(sublist, bits*2);
          //log += ' ' + bigInt2str(v, 10) + ' ' + sublist
          //console.log(log);
          add_(x, v);
        }

        return x;
      }

      self['neededItems'] = neededItems;

      self['encode'] = encode;
      self['decode'] = decode;
    }
    return __MultisetCodec;
  })();

  // combinadic functions
  exports['nCk'] = nCk;
  exports['minValues'] = minValues;
  exports['int2cmb'] = int2cmb;
  exports['cmb2int'] = cmb2int;

  // functions from BigInt.js
  exports['bi2str'] = bigInt2str;
  exports['str2bi'] = str2bigInt;
  exports['int2bi'] = int2bigInt;
  exports['equals'] = equals;
  exports['equalsInt'] = equalsInt;
})(typeof exports === 'undefined' ? window['combinadic'] = {} : exports);
