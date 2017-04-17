/**
 * Reduced version of esa_01_newlib.c
 * With Z3 we cannot find division by zero problem.
 */




static const double



one= 1.00000000000000000000e+00,
pi = 3.14159265358979311600e+00,
pio2_hi = 1.57079632679489655800e+00,
pio2_lo = 6.12323399573676603587e-17,
pS0 = 1.66666666666666657415e-01,
pS1 = -3.25565818622400915405e-01,
pS2 = 2.01212532134862925881e-01,
pS3 = -4.00555345006794114027e-02,
pS4 = 7.91534994289814532176e-04,
pS5 = 3.47933107596021167570e-05,
qS1 = -2.40339491173441421878e+00,
qS2 = 2.02094576023350569471e+00,
qS3 = -6.88283971605453293030e-01,
qS4 = 7.70381505559019352791e-02;


 double __ieee754_acos(double x)




{
 double z,p,q,r,w,s,c,df;
     z = x*x;
     p = z*(pS0+z*(pS1+z*(pS2+z*(pS3+z*(pS4+z*pS5)))));
     q = one+z*(qS1+z*(qS2+z*(qS3+z*qS4)));
     r = p/q;
}