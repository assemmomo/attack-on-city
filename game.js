(()=>{
'use strict';
const $=id=>document.getElementById(id);
const ui={main:$('mainMenu'),controls:$('controlsMenu'),pause:$('pauseMenu'),loading:$('loading'),start:$('startBtn'),controlsBtn:$('controlsBtn'),controlsBack:$('controlsBack'),controlsStart:$('controlsStart'),resume:$('resumeBtn'),restart:$('restartBtn'),mainMenu:$('mainMenuBtn'),sensitivity:$('sensitivity'),fpsToggle:$('fpsToggle'),quality:$('quality'),fps:$('fps'),hint:$('hint'),movement:$('movement'),toast:$('toast'),loadbar:$('loadbar'),loadtext:$('loadtext')};
let scene,camera,renderer,clock,raycaster,worldRoot,playerMesh,torso,headCover,arms=[],legs=[],hands=[],grappleDevices=[],cables=[],hookMeshes=[],dustParticles=[];
let erikaPlayer=null, erikaModule=null, erikaLoaded=false;
const staticBoxCandidates=[],windowInstanceData=Array.from({length:6},()=>[]),lanternGlowData=[];
let dustMesh=null,dustDummy=null,dustSpawnTimer=0,shadowLight=null;
const MAX_DUST=48;
const keys=Object.create(null), mouse={x:0,y:0,locked:false};
const colliders=[],targetMeshes=[],grappleTargetMeshes=[],districtCenters=[],solidMeshes=[],roofSurfaces=[],monsters=[],monsterHitMeshes=[],monsterProjectiles=[];
const WORLD={wallRadius:178,wallHeight:32,groundRadius:182};
const ROPE_MAX=95;   // maximum cable length (metres): targets farther than this cannot be hooked
const CLIMB_SPEED=4.0;   // m/s — the Climb_Wall animation speed is matched to this
const player={pos:new THREE.Vector3(4,0,3),vel:new THREE.Vector3(),yaw:0,pitch:0,grounded:false,onWall:false,wallSide:0,wallNormal:new THREE.Vector3(),wallTime:0,sliding:false,climbing:false,slideTime:0,coyote:.0,jumpBuffer:0,eye:1.65,state:'IDLE',airTime:0,landTime:0,stepTime:0,wasGrounded:false,moveSpeed:0,landEvent:0,landImpact:0,spaceLock:false,mantle:null};
const hooks=[{name:'LEFT',side:-1,held:false,mode:'ready',anchor:null,projectile:null,length:0,line:null,tip:null,mesh:null,autoPull:false},{name:'RIGHT',side:1,held:false,mode:'ready',anchor:null,projectile:null,length:0,line:null,tip:null,mesh:null,autoPull:false}];
let grapplePull=null;
let running=false,started=false,paused=false,lastFrame=0,frames=0,fpsNow=0,fpsAt=0,elapsed=0,toasting=0,audioCtx=null,quality=1,lookSensitivity=0.0022,walkBob=0,viewBob=0,viewRoll=0,worldBuilt=false;
const FIRST_PERSON_ENABLED=false;   // set to true to bring the first-person view (and the V key) back; all its code is still here
let thirdPerson=!FIRST_PERSON_ENABLED,cameraPositionInitialized=false,cameraSupportFollowY=.25;
const THIRD_PERSON_DISTANCE=4.2;
let waistTails=[];
// ===================== BOW & ARROW =====================
const BOW={drawTime:.40,minSpeed:170,maxSpeed:380,gravity:0,maxStuck:40,cooldown:.12,stuckTime:30};const BOW_ARROW_RIGHT_OFFSET=.10;
const AMMO={start:15,perWave:2,max:15,cur:15};   // arrows: 10 at the start; every cleared wave refills them and raises the capacity by 2.  Tweak live: AMMO.cur=99
const bow={carry:0,aiming:false,aimW:0,drawing:false,draw:0,cool:0,equip:0,hold:0,group:null,string:null,nocked:null,mats:null,arrows:[],uiKey:''};
const _bowObj=new THREE.Object3D();
function makeArrowMesh(){
 const m=bow.mats;
 if(!bow.geo){
  // Serrated razor wing: (radial, axial) outline with saw teeth and swept-back barbs; same footprint as before (<= .088 radial, .05-.245 axial).
  const ws=new THREE.Shape();ws.moveTo(0,.05);ws.lineTo(.034,.092);ws.lineTo(.026,.108);ws.lineTo(.058,.15);ws.lineTo(.044,.164);ws.lineTo(.088,.222);ws.lineTo(.05,.206);ws.lineTo(.036,.246);ws.lineTo(0,.2);ws.lineTo(0,.05);
  const wing=new THREE.ExtrudeGeometry(ws,{depth:.006,bevelEnabled:false});wing.translate(0,0,-.003);
  wing.applyMatrix4(new THREE.Matrix4().makeBasis(v3(0,1,0),v3(0,0,1),v3(1,0,0)));
  // Bat-wing fletching: jagged black vane, same footprint as the old flat vane.
  const fs=new THREE.Shape();fs.moveTo(0,0);fs.lineTo(.03,.012);fs.lineTo(.02,.05);fs.lineTo(.07,.085);fs.lineTo(.044,.105);fs.lineTo(.066,.15);fs.lineTo(.03,.14);fs.lineTo(.036,.2);fs.lineTo(0,.2);fs.lineTo(0,0);
  const vane=new THREE.ExtrudeGeometry(fs,{depth:.004,bevelEnabled:false});vane.translate(0,0,-.002);
  vane.applyMatrix4(new THREE.Matrix4().makeBasis(v3(0,1,0),v3(0,0,1),v3(1,0,0)));vane.translate(0,0,.59);
  bow.glowTex=hfxTexSafe();
  bow.geo={shaft:new THREE.CylinderGeometry(.011,.011,.58,6),spear:new THREE.ConeGeometry(.03,.2,4),wing,vane,
   collar:new THREE.CylinderGeometry(.02,.015,.05,6),spike:new THREE.ConeGeometry(.012,.075,4),ring:new THREE.TorusGeometry(.0125,.0042,5,10),
   nockSpike:new THREE.ConeGeometry(.012,.05,4),
   trail:new THREE.BufferGeometry().setFromPoints([v3(0,0,.78),v3(0,0,2.5)])};
 }
 const G=bow.geo,g=new THREE.Group();
 const shaft=new THREE.Mesh(G.shaft,m.shaft);shaft.rotation.x=Math.PI/2;shaft.position.z=.51;g.add(shaft);
 for(const z of[.33,.43,.53,.63]){const r=new THREE.Mesh(G.ring,m.ember);r.position.z=z;g.add(r);}   // glowing blood-red bands
 const spear=new THREE.Mesh(G.spear,m.head);spear.rotation.x=-Math.PI/2;spear.rotation.y=Math.PI/4;spear.position.z=.1;g.add(spear);
 for(let i=0;i<4;i++){const f=new THREE.Group();f.rotation.z=i*Math.PI/2+Math.PI/4;f.add(new THREE.Mesh(G.wing,m.head));g.add(f);}
 const collar=new THREE.Mesh(G.collar,m.head);collar.rotation.x=Math.PI/2;collar.position.z=.245;g.add(collar);
 for(let i=0;i<4;i++){const f=new THREE.Group();f.rotation.z=i*Math.PI/2+Math.PI/4;const s=new THREE.Mesh(G.spike,m.head);s.rotation.x=1.15;s.position.set(0,.026,.285);f.add(s);g.add(f);}
 for(let i=0;i<3;i++){const f=new THREE.Group();f.rotation.z=i*Math.PI*2/3+.5;f.add(new THREE.Mesh(G.vane,m.feather));g.add(f);}
 for(let i=0;i<3;i++){const f=new THREE.Group();f.rotation.z=i*Math.PI*2/3+.5;const ns=new THREE.Mesh(G.nockSpike,m.head);ns.rotation.x=Math.PI/2;ns.position.set(0,.0,.775);f.add(ns);g.add(f);}
 const glow=new THREE.Sprite(m.glow);glow.scale.set(.3,.3,1);glow.position.z=.07;g.add(glow);   // ember glow on the head
 const trail=new THREE.Line(G.trail,m.trail);trail.frustumCulled=false;g.add(trail);g.userData.trail=trail;
 g.traverse(o=>{o.frustumCulled=false;o.castShadow=false;o.receiveShadow=false;});
 return g;
}
function hfxTexSafe(){const c=document.createElement('canvas');c.width=c.height=64;const x=c.getContext('2d');const g=x.createRadialGradient(32,32,0,32,32,32);g.addColorStop(0,'rgba(255,200,170,1)');g.addColorStop(.3,'rgba(255,50,30,.7)');g.addColorStop(1,'rgba(160,0,0,0)');x.fillStyle=g;x.fillRect(0,0,64,64);const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;return t;}
// ===================== LONG SWORD =====================
const sword={group:null,e:0,hold:0,lhold:0,runW:0,atk:0};
// First-person sword view. Tweak live from the browser console, e.g.  SWORD_FP.pitchDeg=50  or  SWORD_FP.bobDeg=5
const SWORD_FP={
 pitchDeg:45,       // blade elevation above the horizon (45 = diagonal, up and forward)
 yawDeg:8,          // lean of the blade toward the screen centre
 rollDeg:-10,       // twist around the blade so its flat face turns toward the player
 bobDeg:3,          // tip up/down amplitude while running (degrees); small on purpose
 sprintBobMul:1.5,  // a bit more bob while sprinting
 bobLag:.5,         // phase lag behind the camera bob (radians), gives the sword some weight
 wobble:.5,         // how much of the hand-bone sway is kept (0 = none, 1 = all)
 offX:0,offY:0,offZ:0,                                   // extra nudge of the grip in camera space (metres)
 minX:.10,maxX:.45,minY:-.40,maxY:-.05,minZ:-.90,maxZ:-.38  // the grip is kept inside this box in front of the camera, so it is always on screen
};
// Sword during the 3-hit combo. While a slash clip is playing the blade is locked to the real hand bone (rotation AND position), so it
// travels exactly with the arm: the grip offset is frozen at the pre-attack average instead of washing out, the first-person screen-clamp box
// opens up so the blade can sweep across the view, and the running bob / smoothing lag are faded out.   Tweak live: SWORD_ATK.rigid=0.7
const SWORD_ATK={
 rigid:1,           // 0 = old behaviour (damped sway), 1 = blade fully locked to the hand during the slash
 // ---- slashing while moving -------------------------------------------------------------------------------------------------------
 // The three slash clips are FULL-BODY animations: the hips twist (+-40 deg in slash 1) or spin a whole 360 deg (slashes 2 and 3) and travel
 // 0.5 m / 1.15 m / 2.4 m forward, with the legs stepping to match. The old moving mode threw away the hips + legs and kept only the arms and
 // spine, so the body never twisted or spun and the arm just waved on its own -> it never looked like the standing slash.
 // Now the moving slash plays the very same full-body clip as the standing one; the character plants its feet for the strike (the run momentum is
 // shed quickly) and keeps only a gentle steer. Tweak live from the console, e.g.  SWORD_ATK.moveSpeed=3   or   SWORD_ATK.layered=true
 layered:false,     // true = old behaviour (arms/spine-only slash layered over the running legs)
 moveSpeed:1.7,     // m/s of steering the player keeps during a slash (it fades to about half of this at the middle of the swing)
 travelMul:.3,      // steering multiplier for the lunging slashes (2nd / 3rd): their root motion already carries the player 1.15 m / 2.4 m
 plantRate:12,      // how fast the running momentum is shed when a slash starts (1/s). Higher = stops sooner, lower = longer slide
 fpBox:{minX:-.95,maxX:.95,minY:-.90,maxY:.70,minZ:-1.40,maxZ:-.12}   // first-person grip zone while slashing (camera space, metres)
};
const _wbA=new THREE.Quaternion(),_wbB=new THREE.Quaternion();
function newWobbleSlot(){return{slow:new THREE.Quaternion(),out:new THREE.Quaternion(),inv:new THREE.Quaternion(),init:false,mode:null};}
const swSlot=newWobbleSlot(),bowSlot=newWobbleSlot();
// Rotation of a hand bone relative to its own slow average, expressed in the reference frame (camera / body): lets a held item sway with the real arm animation.
function handWobble(slot,bone,refQ,dt,key,adapt=1){   // adapt<1 freezes the slow average (adapt=0: item rigidly follows the hand)
 if(slot.mode!==key){slot.mode=key;slot.init=false;}
 bone.getWorldQuaternion(_wbA);_wbB.copy(refQ).invert().multiply(_wbA);
 if(!slot.init){slot.slow.copy(_wbB);slot.init=true;}
 slot.slow.slerp(_wbB,(1-Math.exp(-dt/.45))*adapt);
 return slot.out.copy(_wbB).multiply(slot.inv.copy(slot.slow).invert());
}
function erikaNamed(n){const r=erikaPlayer;if(!r)return null;r.named=r.named||{};if(!(n in r.named)){let f=null;r.root.traverse(o=>{if(!f&&o.name===n)f=o;});r.named[n]=f;}return r.named[n];}
const _palm=new THREE.Vector3();
function palmWorld(hand,finger,out){hand.getWorldPosition(out);const f=finger&&erikaNamed(finger);if(f){f.getWorldPosition(_palm);out.lerp(_palm,.55);}return out;}
let weapon='sword',weaponsHidden=false,climbHideT=0;
const climbCam={d:new THREE.Vector3(),mean:new THREE.Vector3(),on:false,tmp:new THREE.Vector3()};   // first-person camera follows the climbing animation
function setWeapon(w){if(weapon===w)return;weapon=w;if(w!=='bow')stopAim();showToast(w==='bow'?'2 — BOW':'1 — SWORD');sound('draw');}
function buildSword(){
 if(sword.group)return;
 const g=new THREE.Group();g.name='LongSword';
 const black=mat(0x050506,.55,.1);
 const dark=new THREE.MeshStandardMaterial({color:0x0b0b0e,roughness:.22,metalness:.7,emissive:0x5a0606,emissiveIntensity:.9});   // same material as the arrow head
 const ember=new THREE.MeshBasicMaterial({color:0xff2a1a});
 const glowMat=new THREE.SpriteMaterial({map:hfxTexSafe(),color:0xff3a22,transparent:true,depthWrite:false,blending:THREE.AdditiveBlending,fog:false});
 // grip (black) with blood-red bands
 const grip=new THREE.Mesh(new THREE.CylinderGeometry(.019,.021,.27,10),black);grip.position.y=-.015;g.add(grip);
 for(let i=0;i<5;i++){const ring=new THREE.Mesh(new THREE.TorusGeometry(.0215,.004,6,12),i%2?black:ember);ring.rotation.x=Math.PI/2;ring.position.y=-.1+i*.045;g.add(ring);}
 const pommel=new THREE.Mesh(new THREE.SphereGeometry(.036,12,10),dark);pommel.position.y=-.17;g.add(pommel);
 // predator cross-guard: black, with barbed tips and a glowing eye
 const guard=new THREE.Mesh(new THREE.BoxGeometry(.27,.032,.05),dark);guard.position.y=.13;g.add(guard);
 for(const sx of[-1,1]){const tip=new THREE.Mesh(new THREE.ConeGeometry(.022,.04,4),dark);tip.position.set(sx*.135,.13,0);tip.rotation.z=-sx*Math.PI/2;g.add(tip);}
 const eye=new THREE.Mesh(new THREE.SphereGeometry(.014,8,6),ember);eye.position.set(0,.13,.028);g.add(eye);
 // long serrated blade (same length and width as before): saw teeth on both edges, swept to a pointed tip, glowing red ridge
 const R=[];for(let i=0;i<8;i++){const yb=.1+i*.12;R.push([.021,yb],[.031,yb+.075]);}R.push([.025,1.1]);
 const sh=new THREE.Shape();sh.moveTo(-.03,0);sh.lineTo(.03,0);for(const p of R)sh.lineTo(p[0],p[1]);sh.lineTo(0,1.27);for(let i=R.length-1;i>=0;i--)sh.lineTo(-R[i][0],R[i][1]);sh.lineTo(-.03,0);
 const bg=new THREE.ExtrudeGeometry(sh,{depth:.012,bevelEnabled:true,bevelSize:.004,bevelThickness:.004,bevelSegments:1});bg.translate(0,0,-.006);
 const blade=new THREE.Mesh(bg,dark);blade.position.y=.146;g.add(blade);
 const ridge=new THREE.Mesh(new THREE.BoxGeometry(.006,1.1,.022),ember);ridge.position.y=.72;g.add(ridge);
 for(const y of[.3,.6,.9]){const gl=new THREE.Sprite(glowMat);gl.scale.set(.22,.22,1);gl.position.set(0,y+.146,.02);g.add(gl);}   // ember glow along the blade
 g.traverse(o=>{o.castShadow=false;o.receiveShadow=false;o.frustumCulled=false;});
 g.visible=false;scene.add(g);sword.group=g;
}
const _swUp=new THREE.Vector3(0,1,0),_swQ=new THREE.Quaternion(),_swQ2=new THREE.Quaternion(),_swE=new THREE.Euler(),_swP=new THREE.Vector3(),_swP2=new THREE.Vector3(),_swRel=new THREE.Vector3(),_swRight=new THREE.Vector3(1,0,0),_swFA=new THREE.Quaternion(),_swFB=new THREE.Quaternion(),_swFC=new THREE.Quaternion(),_swFD=new THREE.Quaternion(),_swFE=new THREE.Quaternion();
function updateSwordBase(dt=1/60){
 const g=sword.group;if(!g||!playerMesh||!camera)return;
 sword.e+=((weapon==='bow'?1:0)-sword.e)*.18;sword.hold+=((weapon==='sword'?1:0)-sword.hold)*.2;sword.lhold+=(((weapon==='bow'&&bow.equip<.3)?1:0)-sword.lhold)*.2;
 const e=sword.e;
 // slash blend = the same weight the slash clip has in the pose, so the blade is locked to the hand exactly as much as the arm is playing the clip
 const an=erikaAnim,atk=(an&&an.ready&&weapon==='sword')?THREE.MathUtils.clamp((an.attackWeight||0)*SWORD_ATK.rigid,0,1):0;sword.atk=atk;
 const rh=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.rightHand,hips=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.hips;
 if(weaponsHidden||(!thirdPerson&&weapon==='bow')){g.visible=false;return;}
 g.visible=true;g.scale.setScalar(1);
 playerMesh.updateMatrixWorld(true);
 const pq=playerMesh.getWorldQuaternion(_swQ2);
 // ---- held in the right fist; the item follows the real hand animation and has subtle running motion
 const ref=thirdPerson?pq:camera.quaternion;
 if(rh)palmWorld(rh,'mixamorigRightHandMiddle1',_swP);else _swP.set(player.pos.x,player.pos.y+1,player.pos.z);
 if(!thirdPerson){
  // ===== FIRST PERSON =====
  // Blade raised SWORD_FP.pitchDeg above the horizon and pointing forward (so the tip is in view); the tip rises and falls a little while running.
  const F=SWORD_FP,D=Math.PI/180,clampV=THREE.MathUtils.clamp;
  const running=player.grounded&&!player.sliding&&player.moveSpeed>.65;
  sword.runW+=((running?1:0)-sword.runW)*(1-Math.exp(-9*dt));   // eases in/out instead of snapping when you start/stop running
  const sprinting=player.state==='SPRINTING';
  const bobAmt=sword.runW*clampV(player.moveSpeed/(sprinting?14:8),0,1)*(sprinting?F.sprintBobMul:1);
  // grip = the real palm (+ the old 8 cm lift; dips while swapping weapons), a little stride bob, then kept inside a zone of the camera view
  _swP.y+=.08*(1-atk)-e*.6;   // the 8 cm lift fades out while slashing so the grip sits in the real palm
  _swRel.copy(_swP).sub(camera.position).applyQuaternion(_swFE.copy(camera.quaternion).invert());
  _swRel.x+=Math.sin(walkBob*.5)*sword.runW*.012*(1-atk)+F.offX;
  _swRel.y+=Math.sin(walkBob)*sword.runW*.018*(1-atk)+F.offY;
  _swRel.z+=F.offZ;
  {const W=SWORD_ATK.fpBox,L=(a,b)=>a+(b-a)*atk;   // the keep-on-screen box opens up as the slash takes over, so the real arc is not squashed
   _swRel.set(clampV(_swRel.x,L(F.minX,W.minX),L(F.maxX,W.maxX)),clampV(_swRel.y,L(F.minY,W.minY),L(F.maxY,W.maxY)),clampV(_swRel.z,L(F.minZ,W.minZ),L(F.maxZ,W.maxZ)));}
  _swP.copy(_swRel).applyQuaternion(camera.quaternion).add(camera.position);
  // orientation in camera space = lean toward centre * raise blade * roll about the blade axis
  _swFA.setFromAxisAngle(_swUp,F.yawDeg*D).multiply(_swFB.setFromAxisAngle(_swRight,(F.pitchDeg-90)*D)).multiply(_swFC.setFromAxisAngle(_swUp,F.rollDeg*D));
  const held=_swFD.copy(camera.quaternion);
  if(rh)held.multiply(_swFC.identity().slerp(handWobble(swSlot,rh,camera.quaternion,dt,'fp',1-atk),F.wobble+(1-F.wobble)*atk));   // slash: full hand rotation, frozen grip offset
  held.multiply(_swFA);
  if(!sword.q||!sword.fp){sword.q=held.clone();}
  {const kq=1-Math.exp(-26*dt);sword.q.slerp(held,kq+(1-kq)*atk);}sword.fp=true;   // no smoothing lag while slashing
  // tip bob: pitch about the camera's right axis at footstep rate, applied after the smoothing so it stays crisp
  _swFB.setFromAxisAngle(_swRight,F.bobDeg*D*bobAmt*(1-atk)*Math.cos(walkBob*2-F.bobLag));
  _swFC.copy(camera.quaternion).multiply(_swFB).multiply(_swFE);   // cam * Rx(bob) * cam^-1  (_swFE still holds cam^-1)
  g.position.copy(_swP);g.quaternion.copy(_swFC).multiply(sword.q);return;
 }
 // ---- third person (unchanged): held in the right fist, follows the real hand animation
 const heldBase=new THREE.Quaternion().setFromEuler(_swE.set(Math.PI+Math.PI/4,1.5708,0));
 const held=new THREE.Quaternion().copy(ref);
 if(rh)held.multiply(handWobble(swSlot,rh,ref,dt,'tp',1-atk));   // slash: grip offset frozen -> blade rotates exactly with the hand/forearm
 held.multiply(heldBase);
 sword.fp=false;
 // ---- sheathed: left hip, blade pointing down and back
 if(hips)hips.getWorldPosition(_swP2);else _swP2.set(player.pos.x,player.pos.y+1,player.pos.z);
 _swP2.add(new THREE.Vector3(.2,-.05,.16).applyQuaternion(pq));
 const sheath=new THREE.Quaternion().copy(pq).multiply(_swQ.setFromEuler(_swE.set(2.0,0,.55)));
 g.position.lerpVectors(_swP,_swP2,e);g.quaternion.slerpQuaternions(held,sheath,e);
}
function buildBow(){
 if(bow.group)return;
 const glowTexInit=hfxTexSafe();
 bow.mats={wood:new THREE.MeshStandardMaterial({color:0x1d120d,roughness:.5,metalness:.15,emissive:0x3a0505,emissiveIntensity:.8}),grip:mat(0x120c0a,.85),shaft:mat(0x050505,.4,.3),
  head:new THREE.MeshStandardMaterial({color:0x0b0b0e,roughness:.22,metalness:.7,emissive:0x5a0606,emissiveIntensity:.9}),
  feather:new THREE.MeshStandardMaterial({color:0x050505,roughness:.9,emissive:0x2a0000,emissiveIntensity:.8,side:THREE.DoubleSide}),
  ember:new THREE.MeshBasicMaterial({color:0xff2a1a}),bone:mat(0xcfc6b0,.6,.05),
  glow:new THREE.SpriteMaterial({map:glowTexInit,color:0xff3a22,transparent:true,depthWrite:false,blending:THREE.AdditiveBlending,fog:false}),
  trail:new THREE.LineBasicMaterial({color:0xc01818,transparent:true,opacity:.55,depthWrite:false})};
 const g=new THREE.Group();g.name='ArcherBow';
 const curve=new THREE.CatmullRomCurve3([v3(0,-.66,.06),v3(0,-.5,-.04),v3(0,-.25,-.10),v3(0,0,-.115),v3(0,.25,-.10),v3(0,.5,-.04),v3(0,.66,.06)]);
 g.add(new THREE.Mesh(new THREE.TubeGeometry(curve,24,.0155,6,false),bow.mats.wood));
 // Predator bow: bone thorns along both limbs (pointing outward/forward), barbed limb tips, blood-red bindings and a glowing eye at the riser.
 {const thorn=new THREE.ConeGeometry(.0085,.04,5);
  for(const sg of[-1,1])for(const t of[.22,.38,.54,.7,.84]){const p=curve.getPoint(sg<0?t*.5:.5+t*.5),tg=curve.getTangent(sg<0?t*.5:.5+t*.5);
   const th=new THREE.Mesh(thorn,bow.mats.bone);th.position.copy(p).add(v3(0,0,-.02));th.quaternion.setFromUnitVectors(v3(0,1,0),v3(0,.25*sg,-1).normalize());g.add(th);}
  for(const sg of[-1,1]){const tip=new THREE.Mesh(new THREE.ConeGeometry(.016,.075,5),bow.mats.head);tip.position.set(0,sg*.64,.045);tip.rotation.x=-Math.PI/2;g.add(tip);   // limb-tip barbs (inside the old limb length)
   for(const y of[.5,.6]){const r=new THREE.Mesh(new THREE.TorusGeometry(.0195,.0058,5,10),bow.mats.ember);const q=curve.getPoint(.5+sg*(y-.1));r.position.copy(q);r.rotation.x=Math.PI/2;g.add(r);}}
  const eye=new THREE.Mesh(new THREE.SphereGeometry(.017,10,8),bow.mats.ember);eye.position.set(0,0,-.16);g.add(eye);
  const guard=new THREE.Mesh(new THREE.BoxGeometry(.012,.11,.05),bow.mats.head);guard.position.set(0,0,-.145);g.add(guard);}
 const grip=new THREE.Mesh(new THREE.CylinderGeometry(.024,.024,.17,8),bow.mats.grip);grip.position.set(0,0,-.115);g.add(grip);
 const string=new THREE.Line(new THREE.BufferGeometry().setFromPoints([v3(0,.66,.06),v3(0,0,.06),v3(0,-.66,.06)]),new THREE.LineBasicMaterial({color:0xd8342a}));string.frustumCulled=false;g.add(string);bow.string=string;
 const nocked=makeArrowMesh();nocked.userData.trail.visible=false;nocked.visible=false;g.add(nocked);bow.nocked=nocked;
 g.traverse(o=>{o.frustumCulled=false;o.castShadow=false;o.receiveShadow=false;});
 scene.add(g);bow.group=g;
}
const SWORD_ATTACK_SPEED=1.5,SWORD_COMBO_WINDOW=900;
// Fast 3-hit combo. Tweak live from the console, e.g.  SWORD_FAST.speed=[3,3,2.6]   SWORD_FAST.cancelAt=[.4,.4]
// speed = playback rate of slash 1/2/3 | cancelAt = fraction of a slash after which the next click cuts straight into the next slash | buffer = early-click memory (s)
const SWORD_FAST={speed:[2.7,2.6,2.3],cancelAt:[.5,.5,.5],buffer:.5,blend:.07,stop:[.04,.05,.09]};
const swordSpeedFor=n=>SWORD_FAST.speed[n==='SecondSwordSlash'?1:n==='ThirdSwordSlash'?2:0]||SWORD_ATTACK_SPEED;
function swordSlashOK(){return running&&!player.kick&&weapon==='sword'&&!player.slam&&player.grounded&&!player.sliding&&!player.climbing&&!player.onWall&&!player.postFlight&&!(grapplePull&&grapplePull.active);}
function swordSlashU(A){const a=A.attackAction;return a?a.time/Math.max(.1,a.getClip().duration):1;}
function swordChain(A){const step=(A.comboStep+1)%3,name=['SwordSlash','SecondSwordSlash','ThirdSwordSlash'][step];if(!A.attackActs[name])return false;if(player.dash)return false;
 {const dm=pickDashTarget();if(dm){A.attackAction=null;A.attackTarget=0;A.comboUntil=0;A.slashQ=0;startSwordDash(dm,step);return true;}}   // monster under the crosshair within 4 m: dash into the 2nd / 3rd slash too
 A.comboStep=step;A.comboUntil=0;A.slashQ=0;return startErikaSwordAttack(name);}
function swordPump(A,dt){   // every frame: buffered click -> next slash, crossfade between slashes, tiny hit-stop
 const now=performance.now();
 if(A.slashQ){if(now>A.slashQ)A.slashQ=0;else if(A.comboStep>=0&&A.comboStep<=2&&swordSlashOK()){if(A.attackAction?swordSlashU(A)>=SWORD_FAST.cancelAt[A.comboStep]:A.comboUntil>0)swordChain(A);}}
 if(A.atkPrev){A.xfade=Math.min(1,(A.xfade||0)+dt/SWORD_FAST.blend);if(A.xfade>=1){A.atkPrev.stop();if(A.atkPrevUp)A.atkPrevUp.stop();A.atkPrev=A.atkPrevUp=null;}}
 if(A.hitStopT>0&&A.attackAction){A.hitStopT-=dt;const ts=A.hitStopT>0?.06:swordSpeedFor(A.attackName);for(const a of [A.atkFull,A.atkUpper])if(a)a.setEffectiveTimeScale(ts);}
}
// ===================== SWORD HIT EFFECTS =====================
const HFX={ready:false,sparks:[],flashes:[],rings:[],arcs:[],tmp:new THREE.Vector3()};
function hfxTex(kind){const c=document.createElement('canvas');c.width=c.height=128;const x=c.getContext('2d');
 if(kind==='glow'){const g=x.createRadialGradient(64,64,0,64,64,64);g.addColorStop(0,'rgba(255,255,255,1)');g.addColorStop(.3,'rgba(255,214,140,.75)');g.addColorStop(1,'rgba(255,120,40,0)');x.fillStyle=g;x.fillRect(0,0,128,128);}
 else if(kind==='ring'){const g=x.createRadialGradient(64,64,40,64,64,62);g.addColorStop(0,'rgba(255,255,255,0)');g.addColorStop(.7,'rgba(255,235,190,.95)');g.addColorStop(1,'rgba(255,150,60,0)');x.fillStyle=g;x.beginPath();x.arc(64,64,62,0,7);x.fill();}
 else{x.fillStyle='#fff';x.shadowColor='rgba(255,200,120,1)';x.shadowBlur=14;x.beginPath();x.moveTo(8,90);x.quadraticCurveTo(64,-6,120,38);x.quadraticCurveTo(66,30,8,90);x.fill();}
 const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;return t;}
function hfxSparkPoints(F,tex,n){
 const geo=new THREE.BufferGeometry();
 geo.setAttribute('position',new THREE.BufferAttribute(new Float32Array(n*3),3));
 geo.setAttribute('aSize',new THREE.BufferAttribute(new Float32Array(n),1));
 geo.setAttribute('aAlpha',new THREE.BufferAttribute(new Float32Array(n),1));
 geo.setAttribute('aCol',new THREE.BufferAttribute(new Float32Array(n*3),3));
 const mt=new THREE.ShaderMaterial({transparent:true,depthWrite:false,depthTest:false,blending:THREE.AdditiveBlending,uniforms:{uMap:{value:tex},uScale:{value:600}},
  vertexShader:'attribute float aSize;attribute float aAlpha;attribute vec3 aCol;varying float vA;varying vec3 vC;uniform float uScale;void main(){vA=aAlpha;vC=aCol;vec4 mv=modelViewMatrix*vec4(position,1.);gl_PointSize=min(aSize*uScale/max(1.,-mv.z),200.);gl_Position=projectionMatrix*mv;}',
  fragmentShader:'uniform sampler2D uMap;varying float vA;varying vec3 vC;void main(){vec4 t=texture2D(uMap,gl_PointCoord);float a=t.a*vA;if(a<.004)discard;gl_FragColor=vec4(t.rgb*vC,a);\n#include <tonemapping_fragment>\n#include <colorspace_fragment>\n}'});
 const pts=new THREE.Points(geo,mt);pts.frustumCulled=false;pts.renderOrder=20;scene.add(pts);F.pts=pts;
 // light objects with the same interface as a Sprite, so hfxPut and every other caller keep working unchanged
 for(let i=0;i<n;i++)F.sparks.push({s:{position:new THREE.Vector3(),scale:new THREE.Vector3(1,1,1),visible:false,material:{color:new THREE.Color(),opacity:0,rotation:0}},life:0,max:1,v:new THREE.Vector3(),size:1,grow:0,sx:1,grav:0,op:1});
}
function hfxSparkFlush(){
 const F=HFX,P=F.pts;if(!P)return;const A=P.geometry.attributes,n=F.sparks.length;
 for(let i=0;i<n;i++){const o=F.sparks[i].s,k=i*3;
  if(o.visible){A.position.array[k]=o.position.x;A.position.array[k+1]=o.position.y;A.position.array[k+2]=o.position.z;A.aSize.array[i]=o.scale.y;A.aAlpha.array[i]=o.material.opacity;const c=o.material.color;A.aCol.array[k]=c.r;A.aCol.array[k+1]=c.g;A.aCol.array[k+2]=c.b;}
  else{A.aSize.array[i]=0;A.aAlpha.array[i]=0;}}
 A.position.needsUpdate=A.aSize.needsUpdate=A.aAlpha.needsUpdate=A.aCol.needsUpdate=true;
 P.material.uniforms.uScale.value=renderer.domElement.height/(2*Math.tan(camera.fov*Math.PI/360));
}
function swordHitFxInit(){const F=HFX;if(F.ready||!scene)return;F.ready=true;
 const mk=(tex,n,arr)=>{for(let i=0;i<n;i++){const sp=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,transparent:true,opacity:0,depthWrite:false,depthTest:false,fog:false,blending:THREE.AdditiveBlending}));sp.visible=false;sp.renderOrder=20;sp.frustumCulled=false;scene.add(sp);arr.push({s:sp,life:0,max:1,v:new THREE.Vector3(),size:1,grow:0,sx:1,grav:0,op:1});}};
 hfxSparkPoints(F,hfxTex('glow'),420);mk(hfxTex('glow'),4,F.flashes);mk(hfxTex('ring'),4,F.rings);mk(hfxTex('arc'),4,F.arcs);
 for(const arr of [F.flashes,F.rings,F.arcs])for(const p of arr)p.s.visible=true;F.warm=3;}   // warm up the shaders so the first hit does not hitch
function hfxPut(arr,pos,max,size,grow,col){let p=arr[0];for(const q of arr)if(q.life<=0){p=q;break;}
 p.s.position.copy(pos);p.life=p.max=max;p.size=size;p.grow=grow;p.sx=1;p.grav=0;p.v.set(0,0,0);p.s.material.color.setHex(col);p.s.material.rotation=0;p.s.visible=true;return p;}
function swordHitFx(m,step){const F=HFX;if(!F.ready||(m&&m.boss))return;const big=step===2,k=big?1.6:step===1?1.2:1,sc=m.cfg.scale||1;
 const pos=F.tmp.set(m.root.position.x,m.root.position.y+1.35*sc,m.root.position.z);
 const dx=player.pos.x-pos.x,dz=player.pos.z-pos.z,l=Math.hypot(dx,dz)||1;pos.x+=dx/l*.45*sc;pos.z+=dz/l*.45*sc;   // pulled toward the player so it is not buried in the body
 hfxPut(F.flashes,pos,.16,(big?3.4:2.4)*sc,5,0xffe2b0);
 hfxPut(F.rings,pos,.3,.5*sc,(big?9:6)*sc,big?0xffb060:0xffffff);
 const a=hfxPut(F.arcs,pos,.2,(big?3.8:2.8)*sc,3,0xfff0d0);a.sx=1.4;a.s.material.rotation=[-.6,.6,1.57][step]||0;   // slash streak, angle differs per combo hit
 for(let i=0;i<(big?26:16);i++){const p=hfxPut(F.sparks,pos,.28+Math.random()*.3,(.14+Math.random()*.2)*k,0,i%3?0xffc060:0xff7a30);
  const th=Math.random()*6.283,up=Math.random()*.9-.1,sp=(4+Math.random()*7)*k;p.v.set(Math.cos(th)*sp*(1-up*.3),up*sp*.9+1.5,Math.sin(th)*sp*(1-up*.3));p.grav=1;p.grow=-p.size/p.max*.9;}
 slamFx.shake=Math.max(slamFx.shake||0,big?.42:.22);   // camera shake
 erikaAnim.hitStopT=SWORD_FAST.stop[step]||.04;}      // hit-stop
// ---- Arrow effects: muzzle burst on release, ember trail in flight, gore burst on a monster, sparks on walls
function arrowSpark(pos,vel,life,size,col,grav){const p=hfxPut(HFX.sparks,pos,life,size,-size/life*.9,col);p.v.copy(vel);p.grav=grav||0;return p;}
const _afx={p:new THREE.Vector3(),v:new THREE.Vector3(),u:new THREE.Vector3(),w:new THREE.Vector3()};
function arrowReleaseFx(origin,dir,power){const F=HFX;if(!F.ready)return;
 const pos=_afx.p.copy(origin).addScaledVector(dir,.35);
 hfxPut(F.flashes,pos,.14,1.5+power*1.2,5,0xff4a2a);
 hfxPut(F.rings,pos,.22,.3,5+power*3,0xff2a1a);
 const side=_afx.u.set(0,1,0).cross(dir).normalize(),up=_afx.w.copy(dir).cross(side).normalize();
 for(let i=0;i<14+Math.round(power*10);i++){const a=Math.random()*6.283,sp=2+Math.random()*5,fw=6+Math.random()*16*power;
  _afx.v.copy(dir).multiplyScalar(fw).addScaledVector(side,Math.cos(a)*sp).addScaledVector(up,Math.sin(a)*sp);
  arrowSpark(pos,_afx.v,.18+Math.random()*.22,.1+Math.random()*.12,i%3?0xff3a1a:0xffa050,0);}
 slamFx.shake=Math.max(slamFx.shake||0,.05+power*.07);}
function arrowTrailFx(a,from,to,dt){if(!HFX.ready)return;a.emit=(a.emit||0)+dt;if(a.emit<.012)return;a.emit=0;
 for(let i=0;i<2;i++){const t=Math.random();_afx.p.lerpVectors(from,to,t);_afx.v.set((Math.random()-.5)*1.6,(Math.random()-.5)*1.6+.4,(Math.random()-.5)*1.6);
  arrowSpark(_afx.p,_afx.v,.28+Math.random()*.2,.1+Math.random()*.08,i?0xff2a14:0xc01010,0);}}
function arrowHitMonsterFx(pos,dir,m,killed){const F=HFX;if(!F.ready||(m&&m.boss))return;const sc=(m&&m.cfg&&m.cfg.scale)||1;
 hfxPut(F.flashes,pos,.2,(killed?4.2:2.6)*sc,6,0xff2a1a);
 hfxPut(F.rings,pos,.34,.5*sc,(killed?10:6)*sc,0xff1a10);
 const a=hfxPut(F.arcs,pos,.22,(killed?4:2.8)*sc,3,0xff4a2a);a.sx=1.5;a.s.material.rotation=Math.atan2(dir.y,Math.hypot(dir.x,dir.z))+1.57;
 const n=killed?34:22;
 for(let i=0;i<n;i++){const th=Math.random()*6.283,up=Math.random()*1.1-.15,sp=(3+Math.random()*8)*(killed?1.3:1);
  _afx.v.set(Math.cos(th)*sp,up*sp+1.5,Math.sin(th)*sp).addScaledVector(dir,-sp*.7);   // spray back along the shot
  const droplet=i%3===0;arrowSpark(pos,_afx.v,.3+Math.random()*.4,(droplet?.2:.13)+Math.random()*.12,droplet?0x9a0808:i%2?0xff2a14:0xffa050,1.1);}
 slamFx.shake=Math.max(slamFx.shake||0,killed?.3:.16);}
function arrowHitWallFx(pos,dir){const F=HFX;if(!F.ready)return;
 hfxPut(F.flashes,pos,.12,1.1,4,0xffb070);
 for(let i=0;i<10;i++){_afx.v.set(Math.random()-.5,Math.random()*.8,Math.random()-.5).normalize().multiplyScalar(2+Math.random()*5).addScaledVector(dir,-3);arrowSpark(pos,_afx.v,.2+Math.random()*.2,.09+Math.random()*.08,i%2?0xff7a30:0xffd090,1);}}
function swordHitFxUpdate(dt){const F=HFX;if(!F.ready)return;
 if(F.warm>0&&--F.warm===0){for(const arr of [F.flashes,F.rings,F.arcs])for(const p of arr)if(p.life<=0)p.s.visible=false;}
 for(const arr of [F.sparks,F.flashes,F.rings,F.arcs])for(const p of arr){if(p.life<=0)continue;p.life-=dt;if(p.life<=0){p.s.visible=false;p.s.material.opacity=0;continue;}
  p.size=Math.max(.01,p.size+p.grow*dt);if(p.grav)p.v.y-=14*dt;p.s.position.addScaledVector(p.v,dt);p.s.material.opacity=Math.min(1,p.life/p.max*1.6);p.s.scale.set(p.size*p.sx,p.size,1);}
 hfxSparkFlush();}
// ===================== GROUND SLAM (sword + left mouse while jumping / flying) =====================
// Raise the sword overhead with both hands, dive straight down at great speed, plant the blade in the floor and send out a
// shockwave circle that kills every monster inside it.  Tweak live from the console, e.g.  SLAM.radius=20   SLAM.dive=90
const SLAM={
 radius:14,        // shockwave circle radius in metres: every monster inside is hit
 dmgBase:36,       // damage of a slam from almost no height
 dmgPerM:10.8,         // extra damage per metre fallen (monsters: stalker 105 hp, spitter 145, brute 230)
 wind:.2,          // seconds the sword is raised overhead before the dive
 dive:45,          // dive speed in m/s (+25%: was 36)
 impactT:.62,      // seconds the sword stays planted in the ground after the hit
 recoverT:.3,      // seconds the hands take to let go of the sword pose
 killSpeed:42,     // m/s the shockwave travels (monsters die when the ring reaches them)
 maxDive:3.5,      // safety: a dive that never lands is cancelled after this many seconds
 steer:6,          // m/s of WASD steering while diving (only used when the crosshair points at no surface)
 steerMax:37.5     // top horizontal speed while the dive homes in on the crosshair
};
const slamFx={ready:false,all:[],rings:[],decal:null,glow:null,flash:null,wall:null,debris:[],puffs:[],light:null,shake:0,queue:[],warm:0,t:99,
 pos:new THREE.Vector3(),shakeOff:new THREE.Vector3(),blade:new THREE.Vector3(0,1,0)};
const _sl={A:new THREE.Vector3(),B:new THREE.Vector3(),C:new THREE.Vector3(),W:new THREE.Vector3(),T:new THREE.Vector3(),d:new THREE.Vector3(),
 p:new THREE.Vector3(),h:new THREE.Vector3(),dir:new THREE.Vector3(),Bn:new THREE.Vector3(),v1:new THREE.Vector3(),v2:new THREE.Vector3(),
 f:new THREE.Vector3(),r:new THREE.Vector3(),chest:new THREE.Vector3(),G:new THREE.Vector3(),Bd:new THREE.Vector3(),Gd:new THREE.Vector3(),Bu:new THREE.Vector3(),
 X:new THREE.Vector3(),Z:new THREE.Vector3(),UP:new THREE.Vector3(0,1,0),m:new THREE.Matrix4(),q:new THREE.Quaternion(),pq:new THREE.Quaternion()};
// every slam hook runs inside this guard: a bug in the extra effects must never be able to freeze the game loop
function slamSafe(fn,...a){try{return fn(...a);}catch(e){if(!slamSafe.warned){slamSafe.warned=true;console.error('[ground slam]',e);}if(fn===slamPre||fn===slamPost)player.slam=null;}}
function slamLocked(){const s=player.slam;return !!s&&s.phase!=='recover';}
function slamHeightAboveSurface(){let y=0;const px=player.pos.x,pz=player.pos.z;
 for(const c of colliders){if(c.kind==='gable'||c.top<=y||c.top>player.pos.y+.1)continue;if(insideXZ(c,px,pz,.05))y=c.top;}
 const r=roofSurfaceAt(px,pz);if(r!==null&&r<=player.pos.y+.1&&r>y)y=r;return player.pos.y-y;}
// ===================== SUPER STRIKE: every 25 kills the sword gets one charge; press X to slam the ground in front of you =====================
// A long rectangle on the ground in front of the player shows the range (it turns red when monsters are inside, and they get red markers).
// Everything inside dies as the shockwave rushes down the rectangle. Tweak: SUPER.need (kills per charge), SUPER.cap (max stored), SUPER.len / SUPER.wid (metres), SUPER.speed (m/s)
const SUPER={need:25,len:32,wid:15,jump:6,arc:3.2,air:.95/1.4,wind:.3/1.4,impactT:.9/1.4,spd:1.4,rad:4,speed:60,kills:0,last:0,aim:false,bad:0,lock:null,fxT:99,fxOn:false,m:null,markers:[],el:null,forced:false,wasThird:false,flipDirty:false};
// SUPER.wid = strike width (m), SUPER.jump = jump distance (m), SUPER.arc = extra jump height (m), SUPER.air = flight time (s), SUPER.need = kills to charge
function superTex(kind){
 const W=128,H=512,c=document.createElement('canvas');c.width=W;c.height=kind==='front'||kind==='bar'||kind==='ring'?128:H;const x=c.getContext('2d');
 if(kind==='zone'){
  x.fillStyle='rgba(255,255,255,.12)';x.fillRect(0,0,W,H);
  const g=x.createLinearGradient(0,0,W,0);g.addColorStop(0,'rgba(255,255,255,.55)');g.addColorStop(.14,'rgba(255,255,255,0)');g.addColorStop(.86,'rgba(255,255,255,0)');g.addColorStop(1,'rgba(255,255,255,.55)');x.fillStyle=g;x.fillRect(0,0,W,H);
  x.strokeStyle='rgba(255,255,255,.95)';x.lineWidth=6;x.strokeRect(3,3,W-6,H-6);
  x.strokeStyle='rgba(255,255,255,.6)';x.lineWidth=8;for(let y=H-34;y>50;y-=72){x.beginPath();x.moveTo(W*.25,y);x.lineTo(W*.5,y-36);x.lineTo(W*.75,y);x.stroke();}   // chevrons point forward
 }else if(kind==='ring'){const g=x.createRadialGradient(64,64,8,64,64,62);g.addColorStop(0,'rgba(255,255,255,.10)');g.addColorStop(.8,'rgba(255,255,255,.22)');g.addColorStop(1,'rgba(255,255,255,.55)');x.fillStyle=g;x.beginPath();x.arc(64,64,62,0,6.2832);x.fill();x.strokeStyle='rgba(255,255,255,.95)';x.lineWidth=5;x.beginPath();x.arc(64,64,60,0,6.2832);x.stroke();}else if(kind==='bar'){
  const g=x.createLinearGradient(0,0,W,0);g.addColorStop(0,'rgba(255,255,255,0)');g.addColorStop(.5,'rgba(255,255,255,1)');g.addColorStop(1,'rgba(255,255,255,0)');x.fillStyle=g;x.fillRect(0,0,W,128);
 }else if(kind==='front'){
  const g=x.createLinearGradient(0,128,0,0);g.addColorStop(0,'rgba(255,255,255,1)');g.addColorStop(.35,'rgba(255,255,255,.55)');g.addColorStop(1,'rgba(255,255,255,0)');x.fillStyle=g;x.fillRect(0,0,W,128);
  const h=x.createLinearGradient(0,0,W,0);h.addColorStop(0,'rgba(0,0,0,0)');h.addColorStop(.18,'rgba(0,0,0,1)');h.addColorStop(.82,'rgba(0,0,0,1)');h.addColorStop(1,'rgba(0,0,0,0)');x.globalCompositeOperation='destination-in';x.fillStyle=h;x.fillRect(0,0,W,128);
 }else{   // 'crackGlow' / 'crackDark': a jagged fissure down the middle of the rectangle with branches
  let seed=7;const rnd=()=>{seed=(seed*16807)%2147483647;return seed/2147483647;},paths=[];
  let px=W/2;const main=[[px,H]];for(let y=H;y>0;y-=14){px+=(rnd()-.5)*18;px=Math.max(W*.32,Math.min(W*.68,px));main.push([px,y]);}paths.push([main,6]);
  for(let i=0;i<18;i++){const k=1+Math.floor(rnd()*(main.length-2)),dir=rnd()<.5?-1:1;let bx=main[k][0],by=main[k][1];const br=[[bx,by]];const n=4+Math.floor(rnd()*5);for(let j=0;j<n;j++){bx+=dir*(8+rnd()*10);by-=(rnd()-.3)*14;br.push([bx,by]);}paths.push([br,3]);}
  x.lineCap='round';x.lineJoin='round';
  for(const [p,lw] of paths){x.beginPath();p.forEach((q,i)=>i?x.lineTo(q[0],q[1]):x.moveTo(q[0],q[1]));
   if(kind==='crackGlow'){x.strokeStyle='rgba(255,150,70,1)';x.shadowColor='rgba(255,60,20,1)';x.shadowBlur=14;x.lineWidth=lw;}else{x.strokeStyle='rgba(8,4,4,.95)';x.shadowBlur=0;x.lineWidth=lw+3;}
   x.stroke();}
 }
 const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;return t;
}
function superEnsureFx(){
 if(SUPER.m||!scene)return;
 const mk=(tex,add,col,ro)=>{const m=new THREE.Mesh(new THREE.PlaneGeometry(1,1),new THREE.MeshBasicMaterial({map:tex,transparent:true,depthWrite:false,blending:add?THREE.AdditiveBlending:THREE.NormalBlending,side:THREE.DoubleSide,color:col,fog:false,opacity:0,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2}));
  m.rotation.order='YXZ';m.visible=false;m.frustumCulled=false;m.renderOrder=ro;scene.add(m);return m;};
 SUPER.m={ring:mk(superTex('ring'),true,0x8fd0ff,14),zone:mk(superTex('zone'),true,0x8fd0ff,14),flash:mk(superTex('bar'),true,0xff7a3a,15),crackG:mk(superTex('crackGlow'),true,0xffffff,16),scar:mk(superTex('crackDark'),false,0xffffff,13),front:mk(superTex('front'),true,0xff5a2a,17)};
 const mm=new THREE.SpriteMaterial({map:hfxTexSafe(),color:0xff3a22,transparent:true,opacity:.95,depthTest:false,depthWrite:false,blending:THREE.AdditiveBlending,fog:false});
 for(let i=0;i<24;i++){const sp=new THREE.Sprite(mm);sp.visible=false;sp.renderOrder=22;sp.frustumCulled=false;scene.add(sp);SUPER.markers.push(sp);}
}
function superInside(m,src){   // distance along the strike if the monster is inside the rectangle, else -1
 const sy=Math.sin(src.yaw),cy=Math.cos(src.yaw),p=m.root.position,sc=m.cfg.scale,dx=p.x-src.x,dz=p.z-src.z;
 const lf=dx*(-sy)+dz*(-cy),lr=dx*cy+dz*(-sy);
 if(Math.abs(p.y-src.y)>5+sc*2)return -1;
 if((lf<-.45*sc||lf>SUPER.len+.45*sc||Math.abs(lr)>SUPER.wid/2+.45*sc)&&dx*dx+dz*dz>(SUPER.rad+.45*sc)*(SUPER.rad+.45*sc))return -1;
 return Math.max(0,lf);
}
function superPlace(mesh,src,lf0,len,wid,dy){   // lay a flat plane on the ground covering [lf0, lf0+len] in front of src
 const sy=Math.sin(src.yaw),cy=Math.cos(src.yaw),mid=lf0+len/2;
 mesh.position.set(src.x-sy*mid,src.y+dy,src.z-cy*mid);mesh.rotation.set(-Math.PI/2,src.yaw,0);mesh.scale.set(wid,len,1);
}
const _spL={x:0,y:0,z:0,d:0,yaw:0};
const _sfQ1=new THREE.Quaternion(),_sfQ2=new THREE.Quaternion(),_sfV=new THREE.Vector3(),_sfY=new THREE.Vector3(0,1,0),_sfX=new THREE.Vector3(1,0,0),_slUb=new THREE.Vector3();
function superSurfaceAt(x,z,ymax){   // highest floor / roof under (x,z) that is not above ymax
  let y=0;
  for(const c of colliders){if(c.kind==='gable'||c.top>ymax||c.top<=y)continue;if(insideXZ(c,x,z,.05))y=c.top;}
  const r=roofSurfaceAt(x,z);if(r!==null&&r<=ymax&&r>y)y=r;
  return y;
}
// where the jump lands: SUPER.jump metres ahead, shortened if a wall / an edge / the city wall is in the way
function superLanding(x0,y0,z0,yaw,out,dist,arc){
  const fx=-Math.sin(yaw),fz=-Math.cos(yaw),maxR=WORLD.wallRadius-4.3;
  for(let d=(dist||SUPER.jump);d>=0;d-=.25){
    const x=x0+fx*d,z=z0+fz*d;
    if(Math.hypot(x,z)>maxR)continue;
    const ys=superSurfaceAt(x,z,y0+.6);
    if(y0-ys>1)continue;   // would drop off an edge
    let ok=true;
    for(let i=1;i<=12&&ok;i++){
      const u=i/12,px=x0+fx*d*u,pz=z0+fz*d*u,py=y0+(ys-y0)*u+4*(arc===undefined?SUPER.arc:arc)*u*(1-u);
      for(const c of colliders){
        if(c.kind==='roof'||c.kind==='gable'||c.top<.5||c.top<=py+.4)continue;
        if(insideXZ(c,px,pz,.43)){ok=false;break;}
      }
    }
    if(ok){out.x=x;out.y=ys;out.z=z;out.d=d;out.yaw=yaw;return out;}
  }
  out.x=x0;out.y=y0;out.z=z0;out.d=0;out.yaw=yaw;return out;
}
function superCanStart(){
  return running&&!playerDeath.active&&!player.slam&&!player.dash&&!player.kick&&player.grounded&&!player.climbing&&!player.onWall&&!player.sliding&&monsterRespawnTimer<=0&&!(grapplePull&&grapplePull.active);
}
function superReady(){return SUPER.kills>=SUPER.need;}
function startSuperStrike(){   // X: show the strike rectangle (needs a full kill counter)
  if(SUPER.aim||!superReady()||!superCanStart())return;
  if(weapon!=='sword')setWeapon('sword');
  stopAim();SUPER.aim=true;SUPER.bad=0;
}
function superCancelAim(){SUPER.aim=false;}   // right mouse button
function superFire(){   // left mouse button while the rectangle is shown: jump, flip, slam
  if(!SUPER.aim)return;SUPER.aim=false;
  if(!superReady()||!superCanStart())return;
  const A=erikaAnim;
  if(A&&A.attackAction){if(A.atkFull)A.atkFull.stop();if(A.atkUpper)A.atkUpper.stop();A.attackAction=null;A.attackWeight=0;A.attackTarget=0;A.atkFull=null;A.atkUpper=null;A.comboStep=-1;A.comboUntil=0;}
  detachAll(false);stopAim();player.postFlight=false;player.sliding=false;player.jumpBuffer=0;
  const L=superLanding(player.pos.x,player.pos.y,player.pos.z,player.yaw,_spL);
  SUPER.lock={x:L.x,y:L.y,z:L.z,yaw:player.yaw};
  if(!thirdPerson){thirdPerson=true;SUPER.forced=true;SUPER.wasThird=false;cameraPositionInitialized=false;try{applyCharacterViewMode();}catch(e){}}   // the jump has to be visible
  player.slam={phase:'wind',t:0,w:0,k:0,age:0,top:player.pos.y,super:true,flip:0,tuck:0,ft:0,p0:null,cr:0};
  try{slamSound('whoosh');}catch(e){}
}
function superFlying(){const s=player.slam;return !!(s&&s.super&&s.phase==='fly'&&s.p0&&SUPER.lock);}
function superPre(s,dt){   // slamPre branch: wind-up (sword raised), then the scripted jump (superFlyTick), then impact / recover
  const Lk=SUPER.lock;if(!Lk){player.slam=null;return;}
  player.yaw=Lk.yaw;player.jumpBuffer=0;   // the body keeps facing the strike
  if(s.phase==='wind'){
    player.vel.x=0;player.vel.z=0;if(s.jstrike)player.vel.y=.4;
    if(s.t>=(s.windT||SUPER.wind)){s.phase='fly';s.t=0;s.ft=0;s.p0={x:player.pos.x,y:player.pos.y,z:player.pos.z};try{slamSound('dive');}catch(e){}}
  }else if(s.phase==='impact'){
    player.vel.x=0;player.vel.z=0;
    if(s.t>=(s.impT||SUPER.impactT)){s.phase='recover';s.t=0;}
  }else if(s.phase==='recover'){player.vel.x=0;player.vel.z=0;}
  if(s.phase!=='fly'){s.flip=0;s.tuck+=(0-s.tuck)*(1-Math.exp(-14*dt));s.k+=((s.phase==='impact'||s.phase==='recover'?1:0)-s.k)*(1-Math.exp(-30*dt));}
  const wT=s.phase==='recover'?0:1;s.w+=(wT-s.w)*(1-Math.exp(-(wT?16:(s.jstrike?22:9*SUPER.spd))*dt));
  // landing crouch (knees bent): drops in on touch-down, eases out during the recovery
  if(s.phase==='impact')s.cr+=(1-s.cr)*(1-Math.exp(-28*dt));else if(s.phase==='recover')s.cr+=(0-s.cr)*(1-Math.exp(-(s.jstrike?9:8*SUPER.spd)*dt));else s.cr=0;
  if(s.phase==='recover'&&s.t>=(s.jstrike?JSTRIKE.recover:SLAM.recoverT/SUPER.spd)&&s.w<.03&&!(s.cr>.012))player.slam=null;
}
function superFlySafe(dt){try{superFlyTick(dt);}catch(e){console.error('[super strike]',e);player.slam=null;player.vel.set(0,0,0);}}
function superFlyTick(dt){   // replaces resolveMovement while flying: fixed arc from the take-off point to the landing point
  const s=player.slam,L=SUPER.lock,P=player,p0=s.p0,T=s.air||SUPER.air,AR=(s.arc===undefined?SUPER.arc:s.arc);
  s.ft=Math.min(T,s.ft+dt);const u=s.ft/T,sm=THREE.MathUtils.smoothstep;
  P.pos.x=p0.x+(L.x-p0.x)*u;P.pos.z=p0.z+(L.z-p0.z)*u;
  P.pos.y=p0.y+(L.y-p0.y)*u+4*AR*u*(1-u);
  P.vel.set((L.x-p0.x)/T,(L.y-p0.y)/T+4*AR*(1-2*u)/T,(L.z-p0.z)/T);
  P.grounded=false;P.airTime+=dt;P.sliding=false;P.onWall=false;P.climbing=false;
  s.flip=Math.PI*2*sm(u,.12,.78);                              // one full forward somersault, finished before touch-down
  s.tuck=sm(u,0,.12)*(1-sm(u,.9,1));                        // knees tucked during the flip
  s.k=sm(u,.7,.97);                                            // sword swings from overhead down to the ground
  if(u>=1){
    P.pos.set(L.x,L.y,L.z);P.vel.set(0,0,0);P.grounded=true;P.airTime=0;P.coyote=.12;
    s.flip=0;s.tuck=0;s.k=1;s.cr=.6;s.phase='impact';s.t=0;
    if(s.jstrike)jstrikeImpact();else superImpact();
  }
}
// whole-body somersault: the mesh turns around the hip, forward over the head (called from syncPlayerVisuals and slamPoseIK)
function superBodyApply(yy){
  if(!playerMesh)return;
  const s=player.slam;
  if(s&&s.super&&s.flip>1e-3){
    _sfQ1.setFromAxisAngle(_sfY,yy);_sfQ2.setFromAxisAngle(_sfX,-s.flip);_sfQ1.multiply(_sfQ2);
    playerMesh.quaternion.copy(_sfQ1);
    _sfV.set(0,.95,0).applyQuaternion(_sfQ1);
    playerMesh.position.set(player.pos.x-_sfV.x,player.pos.y+.95-_sfV.y,player.pos.z-_sfV.z);
    SUPER.flipDirty=true;
  }else if(SUPER.flipDirty){playerMesh.rotation.set(0,yy,erikaAnim.tilt||0);SUPER.flipDirty=false;}
}
const _crF=[new THREE.Vector3(),new THREE.Vector3()];
function superCrouchDrop(){   // metres the whole body sinks while crouching on landing (applied in syncPlayerVisuals / slamPoseIK so it is not overwritten)
  const s=player.slam;
  return(s&&s.super&&s.cr>.001&&!(s.flip>1e-3))?(s.jstrike?JSTRIKE.crouch:.28)*Math.min(1,s.cr):0;
}
function superCrouchIK(cr,f,r){   // hips are already lowered: put both feet flat on the ground (fixed stance) and bend the knees forward
  const bn=erikaPlayer.bones;
  if(!bn.leftUpLeg||!bn.leftLeg||!bn.leftFoot||!bn.rightUpLeg||!bn.rightLeg||!bn.rightFoot)return;
  playerMesh.updateMatrixWorld(true);
  const gy=player.pos.y+.1;
  _crF[0].set(player.pos.x,gy,player.pos.z).addScaledVector(r,-.17).addScaledVector(f,.14);
  _crF[1].set(player.pos.x,gy,player.pos.z).addScaledVector(r,.17).addScaledVector(f,-.06);
  kickLegIK(bn.leftUpLeg,bn.leftLeg,bn.leftFoot,_crF[0],f,1);
  kickLegIK(bn.rightUpLeg,bn.rightLeg,bn.rightFoot,_crF[1],f,1);
  playerMesh.updateMatrixWorld(true);
}
function superLegsIK(w,U){   // tucked legs for the somersault
  const bn=erikaPlayer.bones,S=_sl;
  if(!bn.leftUpLeg||!bn.leftLeg||!bn.leftFoot||!bn.rightUpLeg||!bn.rightLeg||!bn.rightFoot)return;
  for(const side of [-1,1]){
    const up=side<0?bn.leftUpLeg:bn.rightUpLeg,kn=side<0?bn.leftLeg:bn.rightLeg,ft=side<0?bn.leftFoot:bn.rightFoot;
    up.getWorldPosition(S.A);
    S.T.copy(S.A).addScaledVector(S.f,.34).addScaledVector(U,-.42).addScaledVector(S.r,side*.1);
    kickLegIK(up,kn,ft,S.T,S.f,w);
  }
}
function superImpact(){
 superEnsureFx();const Lk=SUPER.lock,M=SUPER.m;if(!Lk)return;SUPER.kills=0;   // the kill counter goes back to zero
 for(const m of monsters){
  if(!m.alive)continue;const d=superInside(m,Lk);if(d<0)continue;
  if(slamFx.ready)slamFx.queue.push({m,left:d/SUPER.speed,d,dmg:99999,sup:true});else damageMonster(m,99999,'sword');   // the shockwave kills each monster as it reaches it
 }
 SUPER.last=monsterKills;   // kills made by this strike do not count for the next one
 try{slamSound('boom');}catch(e){}
 slamFx.shake=1;
 SUPER.fxOn=true;SUPER.fxT=0;
 superPlace(M.flash,Lk,-1.5,SUPER.len+3,SUPER.wid+5,.09);superPlace(M.crackG,Lk,0,SUPER.len,SUPER.wid,.1);superPlace(M.scar,Lk,0,SUPER.len,SUPER.wid,.06);
 for(const k of['flash','crackG','scar','front'])M[k].visible=true;
 if(slamFx.light){const sy=Math.sin(Lk.yaw),cy=Math.cos(Lk.yaw);slamFx.light.position.set(Lk.x-sy*SUPER.len*.3,Lk.y+2.2,Lk.z-cy*SUPER.len*.3);slamFx.t=0;}
 if(HFX.ready){   // burst at the blade
  const c=new THREE.Vector3(Lk.x-Math.sin(Lk.yaw)*1.4,Lk.y+.5,Lk.z-Math.cos(Lk.yaw)*1.4);
  hfxPut(HFX.flashes,c,.25,7,10,0xffb070);hfxPut(HFX.rings,c,.5,1,16,0xff4a2a);hfxPut(HFX.rings,c,.7,1,26,0xffd0a0);
  for(let i=0;i<40;i++){const a=Math.random()*6.283,sp=5+Math.random()*12,p=hfxPut(HFX.sparks,c,.5+Math.random()*.6,.2+Math.random()*.3,0,i%3?0xff5a2a:0xffe0b0);p.v.set(Math.cos(a)*sp,4+Math.random()*10,Math.sin(a)*sp);p.grav=1;p.grow=-p.size/p.max*.9;}
 }
}
function superPreviewUpdate(dt){
  superEnsureFx();const M=SUPER.m;if(!M)return;
  const s=player.slam,locked=!!(s&&s.super&&!s.jstrike&&(s.phase==='wind'||s.phase==='fly')&&SUPER.lock);
  const show=running&&!playerDeath.active&&(SUPER.aim||locked);
  if(!show){M.zone.visible=false;M.ring.visible=false;for(const sp of SUPER.markers)sp.visible=false;return;}
  const src=locked?SUPER.lock:superLanding(player.pos.x,player.pos.y,player.pos.z,player.yaw,_spL);   // the rectangle starts where the jump lands
  superPlace(M.zone,src,0,SUPER.len,SUPER.wid,.08);M.zone.visible=true;M.ring.position.set(src.x,src.y+.085,src.z);M.ring.rotation.set(-Math.PI/2,0,0);M.ring.scale.set(SUPER.rad*2,SUPER.rad*2,1);M.ring.visible=true;
  let n=0;const now=performance.now();
  for(const m of monsters){
   if(!m.alive||!m.root.visible||n>=SUPER.markers.length)continue;
   if(superInside(m,src)<0)continue;
   const sp=SUPER.markers[n++],p=m.root.position,sc=m.cfg.scale;sp.position.set(p.x,p.y+2.5*sc,p.z);sp.scale.setScalar((.8+.25*Math.sin(now*.012+n))*Math.max(1,sc));sp.visible=true;
  }
  for(let i=n;i<SUPER.markers.length;i++)SUPER.markers[i].visible=false;
  M.zone.material.color.setHex(n>0?0xff3a22:0x8fd0ff);
  M.zone.material.opacity=locked?.95:.5+.22*Math.sin(now*.008);M.ring.material.color.copy(M.zone.material.color);M.ring.material.opacity=M.zone.material.opacity;
}
function superWaveUpdate(dt){
 if(!SUPER.fxOn)return;const M=SUPER.m,Lk=SUPER.lock;if(!M||!Lk){SUPER.fxOn=false;return;}
 const t0=SUPER.fxT;SUPER.fxT+=dt;const t=SUPER.fxT,len=SUPER.len,sy=Math.sin(Lk.yaw),cy=Math.cos(Lk.yaw);
 M.flash.material.opacity=.95*Math.pow(1-Math.min(1,t/.8),2);
 M.crackG.material.opacity=t<.1?t/.1:Math.max(0,1-(t-.1)/2.6);
 M.scar.material.opacity=t<.15?t/.15*.85:(t<7?.85:Math.max(0,.85-(t-7)/3));
 const lf1=Math.min(len,t*SUPER.speed),lf0=Math.min(len,t0*SUPER.speed),u=lf1/len;
 M.front.position.set(Lk.x-sy*lf1,Lk.y+3,Lk.z-cy*lf1);M.front.rotation.set(0,Lk.yaw,0);M.front.scale.set(SUPER.wid+3,6,1);
 M.front.material.opacity=t*SUPER.speed>len+4?0:.9*Math.pow(1-u*.7,1);
 if(HFX.ready&&lf1>lf0){   // embers and sparks fly up where the wave is passing
  for(let i=0;i<10;i++){
   const lf=lf0+(lf1-lf0)*Math.random(),lr=(Math.random()-.5)*SUPER.wid,pos=_dfx.p.set(Lk.x-sy*lf+cy*lr,Lk.y+.2,Lk.z-cy*lf-sy*lr);
   const p=hfxPut(HFX.sparks,pos,.5+Math.random()*.6,.18+Math.random()*.28,0,i%3===0?0xffe0b0:i%3===1?0xff5a2a:0xc01810);p.v.set((Math.random()-.5)*5,6+Math.random()*10,(Math.random()-.5)*5);p.grav=1;p.grow=-p.size/p.max*.9;
  }
 }
 if(t>10){for(const k of['flash','crackG','scar','front'])M[k].visible=false;SUPER.fxOn=false;}
}
function superHudUpdate(){
  if(!SUPER.el){
   const st=document.createElement('style');st.textContent="#superHUD{position:fixed;left:204px;bottom:22px;width:112px;display:flex;flex-direction:column;align-items:center;gap:7px;z-index:30;pointer-events:none;font-family:var(--ui);color:var(--txt)}#superHUD .sh-ring{--p:0;position:relative;width:96px;height:96px;border-radius:50%;background:conic-gradient(#ff6a3a calc(var(--p)*1%),rgba(255,255,255,.14) 0);display:flex;align-items:center;justify-content:center;box-shadow:0 8px 28px rgba(0,0,0,.5)}#superHUD .sh-ring::before{content:'';position:absolute;inset:7px;border-radius:50%;background:radial-gradient(circle at 50% 35%,rgba(40,24,26,.96),rgba(10,12,18,.94))}#superHUD .sh-in{position:relative;display:flex;flex-direction:column;align-items:center;line-height:1.15}#superHUD .sh-t{font-weight:800;font-size:12.5px;letter-spacing:.12em;color:#ffd9cf}#superHUD .sh-n{font-size:11px;letter-spacing:.1em;color:rgba(255,255,255,.65);margin-top:2px}#superHUD .sh-key{min-width:30px;text-align:center;border:1px solid rgba(255,255,255,.55);border-radius:6px;padding:1px 9px;font-weight:800;font-size:14px;background:rgba(10,12,18,.8)}#superHUD .sh-sub{font-size:10px;letter-spacing:.1em;line-height:1.4;color:#ffd9cf;text-align:center;white-space:nowrap}#superHUD.ready .sh-ring{background:conic-gradient(#ff6a3a 100%,#ff6a3a 0);animation:superPulse .8s ease-in-out infinite alternate}#superHUD.ready .sh-t{color:#fff}#superHUD.ready .sh-key{border-color:#ff7a4a;color:#ffb49a}@keyframes superPulse{from{box-shadow:0 0 8px rgba(255,70,40,.35)}to{box-shadow:0 0 28px rgba(255,90,50,.95)}}body:has(.overlay:not(.hidden)) #superHUD{display:none!important}";
   document.head.appendChild(st);
   const el=document.createElement('div');el.id='superHUD';el.innerHTML='<div class="sh-ring"><div class="sh-in"><span class="sh-t">ULTIMATE</span><span class="sh-n"></span></div></div><div class="sh-key">X</div><div class="sh-sub"></div>';document.body.appendChild(el);
   SUPER.el=el;SUPER.ring=el.querySelector('.sh-ring');SUPER.num=el.querySelector('.sh-n');SUPER.sub=el.querySelector('.sh-sub');SUPER.hk='';
  }
  SUPER.el.style.display=running&&!playerDeath.active?'flex':'none';
  const ready=superReady(),busy=!!(player.slam&&player.slam.super),key=[ready,SUPER.kills,SUPER.aim,busy].join('|');
  if(key!==SUPER.hk){SUPER.hk=key;SUPER.ring.style.setProperty('--p',((ready?1:SUPER.kills/SUPER.need)*100).toFixed(1));
   SUPER.num.textContent=ready?'READY':SUPER.kills+' / '+SUPER.need;
   SUPER.sub.textContent=busy?'':SUPER.aim?'LEFT CLICK: STRIKE · RIGHT CLICK: CANCEL':'';
   SUPER.el.classList.toggle('ready',ready&&!busy);}
}
function superFxUpdate(dt){
  const k=monsterKills,striking=!!(player.slam&&player.slam.super);
  if(k<SUPER.last){SUPER.kills=0;SUPER.last=k;SUPER.aim=false;}   // new run
  else if(k>SUPER.last){if(!striking)SUPER.kills=Math.min(SUPER.need,SUPER.kills+(k-SUPER.last));SUPER.last=k;}
  if(SUPER.aim){   // the aiming state ends when the strike can no longer be started
   if(playerDeath.active)SUPER.aim=false;
   else if(weapon!=='sword'||!superReady()||!superCanStart()){SUPER.bad+=dt;if(SUPER.bad>.15)SUPER.aim=false;}else SUPER.bad=0;
  }
  if(SUPER.forced&&!striking){   // give the first-person camera back
   if(playerDeath.active)playerDeath.wasThird=SUPER.wasThird;
   else{thirdPerson=SUPER.wasThird||!FIRST_PERSON_ENABLED;cameraPositionInitialized=false;try{applyCharacterViewMode();}catch(e){}}
   SUPER.forced=false;
  }
  superHudUpdate();superPreviewUpdate(dt);superWaveUpdate(dt);
}
function superReset(){
  SUPER.kills=0;SUPER.last=0;SUPER.aim=false;SUPER.lock=null;SUPER.fxOn=false;SUPER.forced=false;
  if(SUPER.m){for(const k in SUPER.m)SUPER.m[k].visible=false;for(const sp of SUPER.markers)sp.visible=false;}
}
// ===================== LEAP STRIKE: jump from the ground, then press the left mouse button with the sword =====================
// Same wind-up / somersault / sword-slam animation as the super strike, but the landing makes a SMALL circle: every monster inside is hurt,
// thrown JSTRIKE.rise metres into the air, falls back and lies sprawled on the ground, then gets up again if it survived.
// Tweak: JSTRIKE.radius (circle, m), .dmg (damage), .rise (launch height, m), .grav (monster fall gravity), .fall/.lie (s on the ground), .dist (leap length, m)
const JSTRIKE={radius:5.5,dmg:93,rise:3,grav:22,fall:.25,lie:1.3,dist:4,air:.5,arc:1.8,wind:.07,impact:.3,dy:3,recover:.45,crouch:.36};
function startJumpStrike(){
 if(!running||playerDeath.active||weapon!=='sword'||player.slam||player.kick||player.dash||player.grounded||player.climbing||player.onWall||player.sliding||monsterRespawnTimer>0||(grapplePull&&grapplePull.active))return false;
 const h=slamHeightAboveSurface();if(h<.3||h>4)return false;   // from higher up the normal dive slam is used instead
 const A=erikaAnim;
 if(A&&A.attackAction){if(A.atkFull)A.atkFull.stop();if(A.atkUpper)A.atkUpper.stop();A.attackAction=null;A.attackWeight=0;A.attackTarget=0;A.atkFull=null;A.atkUpper=null;A.comboStep=-1;A.comboUntil=0;}
 detachAll(false);stopAim();player.postFlight=false;player.sliding=false;player.jumpBuffer=0;
 const L=superLanding(player.pos.x,player.pos.y-h,player.pos.z,player.yaw,_spL,JSTRIKE.dist,JSTRIKE.arc);
 SUPER.lock={x:L.x,y:L.y,z:L.z,yaw:player.yaw};
 if(!thirdPerson){thirdPerson=true;SUPER.forced=true;SUPER.wasThird=false;cameraPositionInitialized=false;try{applyCharacterViewMode();}catch(e){}}
 player.slam={phase:'wind',t:0,w:0,k:0,age:0,top:player.pos.y,super:true,jstrike:true,flip:0,tuck:0,ft:0,p0:null,air:JSTRIKE.air,arc:JSTRIKE.arc,windT:JSTRIKE.wind,impT:JSTRIKE.impact,hasTarget:true,cr:0,target:new THREE.Vector3(L.x,L.y,L.z)};
 try{slamSound('whoosh');}catch(e){}try{showToast('LEAP STRIKE!');}catch(e){}
 return true;
}
function jstrikeImpact(){   // the sword hits the ground: small circle, monsters are hurt and thrown up
 const Lk=SUPER.lock;if(!Lk)return;
 slamFx.R=JSTRIKE.radius;slamFx.pos.set(Lk.x,Lk.y,Lk.z);slamFx.t=0;
 try{slamSpawnFx();}catch(e){}
 try{slamSound('boom');}catch(e){}slamFx.shake=Math.max(slamFx.shake||0,.55);
 const v0=Math.sqrt(2*JSTRIKE.grav*JSTRIKE.rise);   // launch speed that reaches exactly JSTRIKE.rise metres
 for(const m of monsters){
  if(!m.alive||m.entry||m.climb||m.roof)continue;
  const p=m.root.position,dx=p.x-Lk.x,dz=p.z-Lk.z,d=Math.hypot(dx,dz);
  if(d>JSTRIKE.radius+.45*m.cfg.scale||Math.abs(p.y-Lk.y)>JSTRIKE.dy)continue;
  damageMonster(m,JSTRIKE.dmg,'sword',true);   // leap strike: no sword sound
  if(m.alive&&!m.boss){   // survivors fly up, come down, lie sprawled and get back up (see monsterDownStep)
   m.down={t:0,init:false,air:true,vy:v0,at:0,tt:0,fall:JSTRIKE.fall,lie:JSTRIKE.lie};if(m.anim)m.anim.attackT=-1;
   try{mnKnock(m,1.2/m.cfg.scale);}catch(e){}
  }
 }
}
function startGroundSlam(){
 if(slamHeightAboveSurface()<=4)return;   // the ground slam needs more than 4 m of height above the surface below
 if(!running||weapon!=='sword'||player.slam||player.grounded||player.climbing||player.onWall||player.sliding||monsterRespawnTimer>0)return;
 const A=erikaAnim;
 if(A&&A.attackAction){   // dropped off a ledge in the middle of a slash: the slam takes over
  if(A.atkFull)A.atkFull.stop();if(A.atkUpper)A.atkUpper.stop();
  A.attackAction=null;A.attackWeight=0;A.attackTarget=0;A.atkFull=null;A.atkUpper=null;A.comboStep=-1;A.comboUntil=0;
 }
 detachAll(false);player.postFlight=false;player.sliding=false;player.jumpBuffer=0;
 player.slam={phase:'wind',t:0,w:0,k:0,age:0,top:player.pos.y};
 slamSound('whoosh');showToast('GROUND SLAM!');
}
// where the crosshair points: first floor / roof the view ray reaches (building tops are flat planes, the rest is the ground at y=0)
const _slAimO=new THREE.Vector3(),_slAimD=new THREE.Vector3();
function slamAimPoint(out){
 if(!camera)return false;
 camera.getWorldPosition(_slAimO);camera.getWorldDirection(_slAimD);
 const o=_slAimO,d=_slAimD;if(d.y>-.03)return false;   // looking at the horizon / sky: no landing spot
 let best=Infinity,by=0;
 {const t=(0-o.y)/d.y;if(t>0){best=t;by=0;}}
 for(const c of colliders){
  if(o.y<=c.top+.05||c.top<=.5)continue;
  const t=(c.top-o.y)/d.y;if(!(t>0)||t>=best)continue;
  if(Math.abs(o.x+d.x*t-c.x)<=c.halfX&&Math.abs(o.z+d.z*t-c.z)<=c.halfZ){best=t;by=c.top;}
 }
 if(!isFinite(best)||best>400)return false;
 out.set(o.x+d.x*best,by,o.z+d.z*best);return true;
}
// physics, before resolveMovement: holds the player at the top of the wind-up, then drives the dive
function slamPre(dt){
 const s=player.slam;if(!s)return;
 s.t+=dt;s.age=(s.age||0)+dt;if(s.age>6){player.slam=null;return;}   // safety: never stay stuck in the slam state
 if(s.super){superPre(s,dt);return;}
 if(s.phase==='wind'||s.phase==='dive'){
  if(player.climbing||player.onWall){player.slam=null;return;}
  if(hooks.some(h=>h.mode!=='ready')||grapplePull)detachAll(false);
 }
 if(s.phase==='wind'||s.phase==='dive'){
  s.top=Math.max(s.top||0,player.pos.y);
  s.target=s.target||new THREE.Vector3();s.hasTarget=slamAimPoint(s.target);   // the landing spot follows the mouse
 }
 if(s.phase==='wind'){
  player.vel.y=1.6;const k=Math.exp(-8*dt);player.vel.x*=k;player.vel.z*=k;
  if(s.t>=SLAM.wind){s.phase='dive';s.t=0;slamSound('dive');}
 }else if(s.phase==='dive'){
  const wish=moveInput();
  player.vel.y=-Math.min(SLAM.dive,15+s.t*162.5);   // acceleration also +25%
  let tx=wish.x*SLAM.steer,tz=wish.z*SLAM.steer;
  if(s.hasTarget){   // fly toward the crosshair: arrive exactly when the fall reaches the target height
   const left=Math.max(.12,(player.pos.y-s.target.y)/Math.max(8,-player.vel.y)),dx=s.target.x-player.pos.x,dz=s.target.z-player.pos.z;
   tx=dx/left;tz=dz/left;const l=Math.hypot(tx,tz);if(l>SLAM.steerMax){tx*=SLAM.steerMax/l;tz*=SLAM.steerMax/l;}
  }
  player.vel.x=THREE.MathUtils.damp(player.vel.x,tx,9,dt);player.vel.z=THREE.MathUtils.damp(player.vel.z,tz,9,dt);
  if(s.t>SLAM.maxDive){player.slam=null;return;}
 }else if(s.phase==='impact'){
  player.vel.x=0;player.vel.z=0;player.jumpBuffer=0;
  if(s.t>=SLAM.impactT){s.phase='recover';s.t=0;}
 }
 const wT=s.phase==='recover'?0:1;s.w+=(wT-s.w)*(1-Math.exp(-(wT?16:9)*dt));
 s.k+=((s.phase==='impact'||s.phase==='recover'?1:0)-s.k)*(1-Math.exp(-30*dt));
 if(s.phase==='recover'&&s.t>=SLAM.recoverT&&s.w<.03)player.slam=null;
}
// physics, after resolveMovement: the moment the dive touches the floor / a roof
function slamPost(dt){
 const s=player.slam;if(!s||s.super||(s.phase!=='dive'&&s.phase!=='wind')||!player.grounded)return;
 slamImpact(s);
}
function slamImpact(s){
 s.phase='impact';s.t=0;
 const P=player.pos,R=SLAM.radius;slamFx.R=0;slamFx.pos.copy(P);slamFx.t=0;
 const fall=Math.max(0,(s.top||P.y)-P.y),dmg=Math.round(SLAM.dmgBase+SLAM.dmgPerM*fall),power=THREE.MathUtils.clamp(fall/25,.3,1);
 let killed=0;
 for(const m of monsters){
  if(!m.alive)continue;
  const dx=m.root.position.x-P.x,dz=m.root.position.z-P.z,d=Math.hypot(dx,dz);
  if(d>R+.45*m.cfg.scale||Math.abs(m.root.position.y-P.y)>5+m.cfg.scale*2)continue;
  slamFx.queue.push({m,left:d/SLAM.killSpeed,d,dmg});killed++;
 }
 slamSound('boom');slamFx.shake=power;slamSpawnFx();
 showToast('GROUND SLAM — '+Math.round(fall)+' m FALL · '+dmg+' DAMAGE');
}
// ---- pose: both hands on the sword, raised overhead (k=0) or planted in the ground in front of the chest (k=1) ----
function slamArmIK(side,target,hint,w){
 const bn=erikaPlayer.bones,up=side<0?bn.leftArm:bn.rightArm,fo=side<0?bn.leftForeArm:bn.rightForeArm,ha=side<0?bn.leftHand:bn.rightHand;if(!up||!fo||!ha)return;
 const finger=side<0?'mixamorigLeftHandMiddle1':'mixamorigRightHandMiddle1',S=_sl;
 for(let pass=0;pass<3;pass++){
  up.getWorldPosition(S.A);fo.getWorldPosition(S.B);ha.getWorldPosition(S.C);
  const L1=S.A.distanceTo(S.B),L2=S.B.distanceTo(S.C);if(L1<1e-4||L2<1e-4)return;
  palmWorld(ha,finger,S.v1);S.d.copy(S.v1).sub(S.C);
  S.W.copy(target).addScaledVector(S.d,-.85);
  S.dir.copy(S.W).sub(S.A);let dist=S.dir.length();if(dist<1e-4)return;S.dir.divideScalar(dist);
  dist=THREE.MathUtils.clamp(dist,Math.abs(L1-L2)+.02,(L1+L2)*.998);
  S.p.copy(hint).addScaledVector(S.dir,-hint.dot(S.dir));if(S.p.lengthSq()<1e-6)S.p.set(0,-1,0).addScaledVector(S.dir,S.dir.y);S.p.normalize();
  const cosA=THREE.MathUtils.clamp((L1*L1+dist*dist-L2*L2)/(2*L1*dist),-1,1),sinA=Math.sqrt(1-cosA*cosA);
  S.Bn.copy(S.A).addScaledVector(S.dir,L1*cosA).addScaledVector(S.p,L1*sinA);
  S.v1.copy(S.B).sub(S.A).normalize();S.v2.copy(S.Bn).sub(S.A).normalize();_ikTurnBone(up,S.v1,S.v2,w);
  fo.getWorldPosition(S.B);ha.getWorldPosition(S.C);S.v1.copy(S.C).sub(S.B).normalize();S.v2.copy(S.W).sub(S.B).normalize();_ikTurnBone(fo,S.v1,S.v2,w);
 }
}
function slamPoseIK(){
 const s=player.slam;if(!s||!(s.w>.01||s.cr>.01)||!erikaPlayer||!erikaPlayer.bones||!playerMesh)return;
 const bn=erikaPlayer.bones,S=_sl,chest=bn.spine2||bn.spine1||bn.spine||bn.hips;if(!chest||!bn.rightArm||!bn.leftArm)return;
 if(s.super){const yy=player.yaw+(erikaAnim.ready&&thirdPerson?erikaAnim.heading+(erikaAnim.aimYawOff||0):0);playerMesh.position.copy(player.pos);playerMesh.position.y-=superCrouchDrop();playerMesh.rotation.y=yy;superBodyApply(yy);}
  playerMesh.updateMatrixWorld(true);chest.getWorldPosition(S.chest);playerMesh.getWorldQuaternion(S.pq);
 S.f.set(0,0,-1).applyQuaternion(S.pq);S.f.y=0;if(S.f.lengthSq()<1e-6)S.f.set(0,0,-1);S.f.normalize();
 S.r.set(1,0,0).applyQuaternion(S.pq);S.r.y=0;if(S.r.lengthSq()<1e-6)S.r.set(1,0,0);S.r.normalize();
 let U=S.UP;if(s.super&&s.flip>1e-3){S.f.set(0,0,-1).applyQuaternion(S.pq).normalize();S.r.set(1,0,0).applyQuaternion(S.pq).normalize();U=_slUb.set(0,1,0).applyQuaternion(S.pq);}   // somersault: use the body's own up / forward
 if(s.super&&s.cr>.01&&!(s.flip>1e-3)){superCrouchIK(Math.min(1,s.cr),S.f,S.r);chest.getWorldPosition(S.chest);}   // bent knees on landing
 const k=THREE.MathUtils.clamp(s.k,0,1);
 // raised: above the head, blade up and tilted a little back.  planted: arms forward, blade pointing straight down into the floor
 S.G.copy(S.chest).addScaledVector(U,.5).addScaledVector(S.f,.2);S.Bd.copy(U).addScaledVector(S.f,-.42).normalize();
 S.Gd.copy(S.chest).addScaledVector(U,-.24).addScaledVector(S.f,.56);S.Bu.copy(U).multiplyScalar(-1).addScaledVector(S.f,.1).normalize();
 S.G.lerp(S.Gd,k);S.Bd.lerp(S.Bu,k).normalize();
 slamFx.blade.copy(S.Bd);
 // right hand just under the guard, left hand under it near the pommel
 S.T.copy(S.G).addScaledVector(S.Bd,.03);S.h.copy(S.r).multiplyScalar(.8).addScaledVector(U,-.5);slamArmIK(1,S.T,S.h,s.w);
 S.T.copy(S.G).addScaledVector(S.Bd,-.11);S.h.copy(S.r).multiplyScalar(-.8).addScaledVector(U,-.5);slamArmIK(-1,S.T,S.h,s.w);
  if(s.super&&s.tuck>.01)superLegsIK(s.tuck,U);
}
// the sword follows the real palms while the pose is active (first and third person)
function slamSwordOverride(dt){
 const s=player.slam,g=sword.group;if(!s||!g||!g.visible||!(s.w>.01)||!erikaPlayer||!erikaPlayer.bones||!playerMesh)return;
 const bn=erikaPlayer.bones,S=_sl;if(!bn.rightHand||!bn.leftHand)return;
 palmWorld(bn.rightHand,'mixamorigRightHandMiddle1',S.v1);palmWorld(bn.leftHand,'mixamorigLeftHandMiddle1',S.v2);
 const B=S.Bd.copy(slamFx.blade).normalize();
 S.T.copy(S.v1).add(S.v2).multiplyScalar(.5).addScaledVector(B,.04);
 playerMesh.getWorldQuaternion(S.pq);S.f.set(0,0,-1).applyQuaternion(S.pq);if(s.super&&s.flip>1e-3)S.f.normalize();else{S.f.y=0;S.f.normalize();}
 S.X.copy(S.f).addScaledVector(B,-S.f.dot(B));if(S.X.lengthSq()<1e-6)S.X.set(1,0,0);S.X.normalize();   // cutting edge faces forward
 S.Z.crossVectors(S.X,B).normalize();S.m.makeBasis(S.X,B,S.Z);S.q.setFromRotationMatrix(S.m);
 const w=THREE.MathUtils.smoothstep(s.w,0,1);
 g.position.lerp(S.T,w);g.quaternion.slerp(S.q,w);
}
// ---- effects -------------------------------------------------------------------------------------------------------------
function slamCanvas(size){const c=document.createElement('canvas');c.width=c.height=size;return c;}
function slamCrackLines(){
 let seed=11;const rnd=()=>{seed=(seed*16807)%2147483647;return seed/2147483647;},lines=[];
 const grow=(px,py,ang,len,wid,depth)=>{const pts=[[px,py]];let cx=px,cy=py,a=ang;const n=Math.max(2,Math.ceil(len/12));
  for(let i=0;i<n;i++){a+=(rnd()-.5)*.6;cx+=Math.cos(a)*12;cy+=Math.sin(a)*12;pts.push([cx,cy]);if(depth>0&&rnd()<.14)grow(cx,cy,a+(rnd()<.5?-1:1)*(.45+rnd()*.7),len*(1-i/n)*.55,wid*.62,depth-1);}
  lines.push({pts,wid});};
 for(let i=0;i<15;i++)grow(256,256,i/15*Math.PI*2+rnd()*.3,150+rnd()*100,6,2);
 return lines;
}
function slamDecalTexture(glow){
 const c=slamCanvas(512),x=c.getContext('2d'),lines=slamCrackLines();
 if(!glow){const g=x.createRadialGradient(256,256,0,256,256,256);g.addColorStop(0,'rgba(18,12,9,.9)');g.addColorStop(.3,'rgba(26,19,14,.6)');g.addColorStop(.7,'rgba(36,28,21,.2)');g.addColorStop(1,'rgba(0,0,0,0)');x.fillStyle=g;x.fillRect(0,0,512,512);}
 x.lineCap='round';x.lineJoin='round';
 for(const L of lines){x.beginPath();L.pts.forEach((p,i)=>i?x.lineTo(p[0],p[1]):x.moveTo(p[0],p[1]));
  if(glow){x.strokeStyle='rgba(255,150,60,.9)';x.lineWidth=L.wid+3;}else{x.strokeStyle='rgba(6,5,4,.96)';x.lineWidth=L.wid;}x.stroke();}
 x.globalCompositeOperation='destination-in';const m=x.createRadialGradient(256,256,0,256,256,256);m.addColorStop(0,'rgba(0,0,0,1)');m.addColorStop(.8,'rgba(0,0,0,1)');m.addColorStop(1,'rgba(0,0,0,0)');x.fillStyle=m;x.fillRect(0,0,512,512);
 const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;return t;
}
function initSlamFx(){
 const F=slamFx;if(F.ready||!scene)return;F.ready=true;F.warm=4;
 const add=(o)=>{o.frustumCulled=false;o.visible=true;scene.add(o);F.all.push(o);return o;};
 const basic=(color,extra)=>new THREE.MeshBasicMaterial(Object.assign({color,transparent:true,opacity:0,depthWrite:false,fog:false,side:THREE.DoubleSide},extra||{}));
 const flat=-Math.PI/2;
 // shockwave rings
 const ringDef=[[.82,1,0xffa94d,.5,1,.95,0],[.93,1,0xfff0d0,.42,1.04,.9,.03],[.55,1,0xff7a2a,.8,.55,.5,0]];
 for(const [i0,o0,col,dur,sc,op,delay] of ringDef){
  const m=add(new THREE.Mesh(new THREE.RingGeometry(i0,o0,72),basic(col,{blending:THREE.AdditiveBlending})));m.rotation.x=flat;m.renderOrder=7;
  F.rings.push({m,dur,sc,op,delay});
 }
 F.flash=add(new THREE.Mesh(new THREE.CircleGeometry(1,40),basic(0xffe0a8,{blending:THREE.AdditiveBlending})));F.flash.rotation.x=flat;F.flash.renderOrder=7;
 // dust wall (open cylinder with a fading top edge)
 {const c=slamCanvas(64),x=c.getContext('2d'),g=x.createLinearGradient(0,0,0,64);g.addColorStop(0,'rgba(215,196,165,0)');g.addColorStop(.35,'rgba(215,196,165,.55)');g.addColorStop(1,'rgba(215,196,165,.95)');x.fillStyle=g;x.fillRect(0,0,64,64);
  const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;
  F.wall=add(new THREE.Mesh(new THREE.CylinderGeometry(1,1,1,56,1,true),basic(0xffffff,{map:t})));F.wall.renderOrder=6;}
 // cracked, scorched ground
 F.decal=add(new THREE.Mesh(new THREE.CircleGeometry(1,48),basic(0xffffff,{map:slamDecalTexture(false),polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2})));F.decal.rotation.x=flat;F.decal.renderOrder=3;
 F.glow=add(new THREE.Mesh(new THREE.CircleGeometry(1,48),basic(0xffffff,{map:slamDecalTexture(true),blending:THREE.AdditiveBlending,polygonOffset:true,polygonOffsetFactor:-3,polygonOffsetUnits:-3})));F.glow.rotation.x=flat;F.glow.renderOrder=4;
 // landing marker: the kill circle and its centre, shown on the spot the crosshair points at while the slam is in the air
 F.mk1=new THREE.Mesh(new THREE.RingGeometry(.965,1,72),basic(0xff5a3c,{blending:THREE.AdditiveBlending}));F.mk1.rotation.x=flat;F.mk1.renderOrder=8;F.mk1.frustumCulled=false;scene.add(F.mk1);
 F.mk2=new THREE.Mesh(new THREE.RingGeometry(.55,1,40),basic(0xffd27a,{blending:THREE.AdditiveBlending}));F.mk2.rotation.x=flat;F.mk2.renderOrder=8;F.mk2.frustumCulled=false;scene.add(F.mk2);
 F.mk1.visible=F.mk2.visible=true;F.mkWarm=true;
 // flying rubble
 const rg=new THREE.BoxGeometry(.2,.2,.2),rm=new THREE.MeshStandardMaterial({color:0x4d4741,roughness:.95});
 for(let i=0;i<40;i++){const m=add(new THREE.Mesh(rg,rm));m.scale.setScalar(1e-4);F.debris.push({m,v:new THREE.Vector3(),spin:new THREE.Vector3(),life:0,size:1});}
 // dust puffs
 {const c=slamCanvas(64),x=c.getContext('2d'),g=x.createRadialGradient(32,32,0,32,32,32);g.addColorStop(0,'rgba(255,255,255,.95)');g.addColorStop(.5,'rgba(255,255,255,.45)');g.addColorStop(1,'rgba(255,255,255,0)');x.fillStyle=g;x.fillRect(0,0,64,64);
  const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;
  for(let i=0;i<22;i++){const sp=add(new THREE.Sprite(new THREE.SpriteMaterial({map:t,color:0xcdbb9f,transparent:true,opacity:0,depthWrite:false,fog:false})));sp.scale.setScalar(1e-4);F.puffs.push({sp,v:new THREE.Vector3(),life:0,max:1,size:1});}}
 // one permanent light (adding / removing lights later would recompile every material): flashes at the impact
 F.light=new THREE.PointLight(0xffa860,0,46,2);F.light.visible=true;scene.add(F.light);
}
function slamSpawnFx(){
 const F=slamFx;if(!F.ready)return;const P=F.pos,R=F.R||SLAM.radius,y=P.y;
 for(const o of F.all)o.visible=true;
 F.t=0;
 F.decal.position.set(P.x,y+.045,P.z);F.glow.position.set(P.x,y+.05,P.z);F.flash.position.set(P.x,y+.07,P.z);
 for(const r of F.rings)r.m.position.set(P.x,y+.08,P.z);
 F.wall.position.set(P.x,y+1.1,P.z);
 for(const d of F.debris){
  const a=Math.random()*Math.PI*2,rad=.5+Math.random()*3.5,sp=4+Math.random()*9;
  d.m.position.set(P.x+Math.cos(a)*rad,y+.1,P.z+Math.sin(a)*rad);d.v.set(Math.cos(a)*sp,6+Math.random()*10,Math.sin(a)*sp);
  d.spin.set((Math.random()-.5)*14,(Math.random()-.5)*14,(Math.random()-.5)*14);d.life=1.1+Math.random()*.7;d.size=.5+Math.random()*1.3;d.m.scale.setScalar(d.size);
 }
 for(const p of F.puffs){
  const a=Math.random()*Math.PI*2,rad=.8+Math.random()*2.2,sp=4+Math.random()*7;
  p.sp.position.set(P.x+Math.cos(a)*rad,y+.5+Math.random()*.6,P.z+Math.sin(a)*rad);p.v.set(Math.cos(a)*sp,.8+Math.random()*1.6,Math.sin(a)*sp);
  p.life=p.max=.9+Math.random()*.7;p.size=2+Math.random()*2.2;
 }
 F.light.position.set(P.x,y+1.4,P.z);
}
function updateSlamFx(dt){
 const F=slamFx;if(!F.ready)return;
 // monsters die when the shockwave reaches them
 for(let i=F.queue.length-1;i>=0;i--){
  const q=F.queue[i];q.left-=dt;if(q.left>0)continue;F.queue.splice(i,1);
  const m=q.m;if(!m.alive)continue;
  damageMonster(m,q.dmg,'sword',!q.sup);if(q.sup&&!m.alive)SUPER.last++;   // ground slam from above: no sword sound (the super strike keeps its own)
  if(!m.alive&&!m.boss){try{mnKnock(m,(3.5+Math.max(0,SLAM.radius-q.d)*.3)/m.cfg.scale);}catch(e){}}
 }
 F.shake=Math.max(0,F.shake-dt*1.9);
 {const s=player.slam,show=!!s&&(s.phase==='wind'||s.phase==='dive'||(s.jstrike&&s.phase==='fly'))&&s.hasTarget&&F.mk1;
  if(F.mk1){if(!F.mkWarm){F.mk1.visible=F.mk2.visible=!!show;}
   if(show){const pulse=.55+.35*Math.sin(performance.now()*.012);F.mk1.position.set(s.target.x,s.target.y+.12,s.target.z);F.mk1.scale.setScalar(s.jstrike?JSTRIKE.radius:SLAM.radius);F.mk1.material.opacity=pulse;
    F.mk2.position.set(s.target.x,s.target.y+.13,s.target.z);F.mk2.scale.setScalar(1.1+.25*Math.sin(performance.now()*.012));F.mk2.material.opacity=.95;}else{F.mk1.material.opacity=0;F.mk2.material.opacity=0;}}}
 if(F.t>=99)return;
 F.t+=dt;const t=F.t,R=F.R||SLAM.radius,ease=u=>1-Math.pow(1-u,3);
 for(const r of F.rings){const u=THREE.MathUtils.clamp((t-r.delay)/r.dur,0,1),on=t>=r.delay;r.m.scale.setScalar(Math.max(1e-3,R*r.sc*ease(u)));r.m.material.opacity=on?r.op*Math.pow(1-u,1.4):0;}
 {const u=THREE.MathUtils.clamp(t/.3,0,1);F.flash.scale.setScalar(Math.max(1e-3,R*.5*ease(u)));F.flash.material.opacity=.95*Math.pow(1-u,2);}
 {const u=THREE.MathUtils.clamp(t/.7,0,1),r=Math.max(1e-3,R*.95*ease(u));F.wall.scale.set(r,1.2+2.8*ease(u),r);F.wall.position.y=F.pos.y+(1.2+2.8*ease(u))/2;F.wall.material.opacity=.65*Math.pow(1-u,1.2);}
 {const u=THREE.MathUtils.clamp(t/.22,0,1),s=R*.62*ease(u);F.decal.scale.setScalar(Math.max(1e-3,s));F.glow.scale.setScalar(Math.max(1e-3,s));
  F.decal.material.opacity=t<6?1:Math.max(0,1-(t-6)/3);F.glow.material.opacity=Math.max(0,1-t/1.6)*.95;}
 if(t>9){for(const o of F.all)o.visible=false;F.t=99;return;}   // everything has faded: stop drawing it
 for(const d of F.debris){
  if(d.life<=0)continue;d.life-=dt;d.v.y-=26*dt;d.m.position.addScaledVector(d.v,dt);d.m.rotation.x+=d.spin.x*dt;d.m.rotation.y+=d.spin.y*dt;d.m.rotation.z+=d.spin.z*dt;
  if(d.m.position.y<F.pos.y+.05&&d.v.y<0){d.v.y*=-.25;d.v.x*=.5;d.v.z*=.5;d.m.position.y=F.pos.y+.06;if(Math.abs(d.v.y)<1)d.life=Math.min(d.life,.25);}
  if(d.life<=0){d.m.scale.setScalar(1e-4);}else if(d.life<.3)d.m.scale.setScalar(d.size*d.life/.3);
 }
 for(const p of F.puffs){
  if(p.life<=0)continue;p.life-=dt;const u=1-Math.max(0,p.life)/p.max;p.v.multiplyScalar(Math.exp(-2.2*dt));p.sp.position.addScaledVector(p.v,dt);
  p.sp.scale.setScalar(p.size*(.5+1.8*Math.sqrt(u)));p.sp.material.opacity=p.life>0?.62*Math.pow(1-u,1.3):0;
  if(p.life<=0){p.sp.material.opacity=0;p.sp.scale.setScalar(1e-4);}
 }
 F.light.intensity=t<.5?120*Math.pow(1-t/.5,2):0;
}
function slamRenderPre(){
 const F=slamFx;if(F.shake>.001&&camera){const a=F.shake*F.shake*.45*(GFX.shake/100);F.shakeOff.set((Math.random()-.5)*a,(Math.random()-.5)*a,(Math.random()-.5)*a);camera.position.add(F.shakeOff);F.shaking=true;}else F.shaking=false;
}
function slamRenderPost(){
 const F=slamFx;if(F.shaking&&camera){camera.position.sub(F.shakeOff);F.shaking=false;}
 if(F.warm>0){F.warm--;if(F.warm===0){for(const o of F.all)o.visible=false;F.mkWarm=false;}}   // first frames render everything once so no shader compiles mid-fight
}
function slamSound(kind){
 try{
  if(!audioCtx)audioCtx=new (window.AudioContext||window.webkitAudioContext)();if(audioCtx.state==='suspended')audioCtx.resume();
  const ac=audioCtx,now=ac.currentTime,out=ac.destination;
  const noise=(dur)=>{const b=ac.createBuffer(1,Math.max(1,Math.floor(ac.sampleRate*dur)),ac.sampleRate),d=b.getChannelData(0);for(let i=0;i<d.length;i++)d[i]=Math.random()*2-1;const s=ac.createBufferSource();s.buffer=b;return s;};
  const burst=(dur,type,f0,f1,q,gain,delay=0)=>{const n=noise(dur),f=ac.createBiquadFilter(),g=ac.createGain(),t0=now+delay;f.type=type;f.Q.value=q;f.frequency.setValueAtTime(f0,t0);f.frequency.exponentialRampToValueAtTime(Math.max(20,f1),t0+dur);
   g.gain.setValueAtTime(.0001,t0);g.gain.exponentialRampToValueAtTime(gain,t0+Math.min(.04,dur*.25));g.gain.exponentialRampToValueAtTime(.0001,t0+dur);n.connect(f);f.connect(g);g.connect(out);n.start(t0);};
  if(kind==='whoosh')burst(.32,'bandpass',500,2000,1.2,.15);
  else if(kind==='dive')burst(.55,'bandpass',3200,700,1.6,.14);
  else{
   const o=ac.createOscillator(),g=ac.createGain();o.type='sine';o.frequency.setValueAtTime(130,now);o.frequency.exponentialRampToValueAtTime(26,now+.8);
   g.gain.setValueAtTime(.0001,now);g.gain.exponentialRampToValueAtTime(.75,now+.012);g.gain.exponentialRampToValueAtTime(.0001,now+.85);o.connect(g);g.connect(out);o.start(now);o.stop(now+.9);
   burst(.7,'lowpass',1400,70,.7,.55);burst(.12,'highpass',1800,3000,.7,.3);burst(.9,'lowpass',500,50,.5,.3,.05);
  }
 }catch(e){}
}
function updateSword(dt=1/60){updateSwordBase(dt);if(player.block&&sword.group)sword.group.visible=false;   // empty hand while guarding
 slamSafe(slamSwordOverride,dt);lungeSafe(lungeSwordOverride,dt);}

const attackRootDisp=new THREE.Vector3();   // forward travel baked into the slash clips, applied to the player each frame
function startErikaSwordAttack(name){
 const A=erikaAnim,action=A.attackActs[name];if(!action)return false;
 if(A.atkPrev){A.atkPrev.stop();if(A.atkPrevUp)A.atkPrevUp.stop();A.atkPrev=A.atkPrevUp=null;}
 if(A.atkFull&&A.atkFull!==action){if(A.attackWeight>.3){A.atkPrev=A.atkFull;A.atkPrevUp=A.atkUpper;A.xfade=0;}else{A.atkFull.stop();if(A.atkUpper)A.atkUpper.stop();}}else if(A.atkUpper)A.atkUpper.stop();
 const upper=A.attackUpper[name]||null;
 for(const a of [action,upper]){if(!a)continue;a.reset();a.setEffectiveTimeScale(swordSpeedFor(name));a.setLoop(THREE.LoopOnce,1);a.clampWhenFinished=true;a.enabled=true;a.setEffectiveWeight(0);a.play();}
 sound('swordGround');
 A.attackAction=action;A.attackName=name;A.atkFull=action;A.atkUpper=upper;A.attackSerial=(A.attackSerial||0)+1;A.attackTarget=1;A.lunged=false;A.slashQ=0;A.hitStopT=0;
 player.jumpBuffer=0;player.sliding=false;   // the player keeps their momentum: attacking no longer freezes movement
 return true;
}
// ===================== SWORD DASH: aim at a monster within 4 m and swing -> rush to it at high speed, then land the first slash =====================
// Tweak: DASH.range (metres), DASH.cool (seconds between dashes, set in startSwordDash)
const DASH={range:8,cool:0,fov:0,op:0,trail:null,core:null,from:new THREE.Vector3(),end:new THREE.Vector3(),dir:new THREE.Vector3(0,0,-1),up:new THREE.Vector3(0,1,0)};
const _dfx={p:new THREE.Vector3(),v:new THREE.Vector3()};
function dashFxInit(){
 if(DASH.trail||!scene)return;
 const mk=(r,col)=>{const g=new THREE.CylinderGeometry(r,.01,1,10,1,true);g.translate(0,-.5,0);   // wide end at the player, thin tail behind
  const m=new THREE.Mesh(g,new THREE.MeshBasicMaterial({color:col,transparent:true,opacity:0,depthWrite:false,blending:THREE.AdditiveBlending,side:THREE.DoubleSide,fog:false}));
  m.visible=false;m.frustumCulled=false;m.renderOrder=19;scene.add(m);return m;};
 DASH.trail=mk(.36,0xff2a1a);DASH.core=mk(.12,0xffe6d6);
}
function pickDashTarget(){
 if(!camera||DASH.cool>0||player.dash)return null;
 const o=camera.position,dir=cameraDir();let best=null,bs=-1;
 for(const m of monsters){
  if(!m.alive||m.entry||!m.root.visible)continue;
  const p=m.root.position,sc=m.cfg.scale,dx=p.x-player.pos.x,dz=p.z-player.pos.z,hd=Math.hypot(dx,dz);
  if(hd>DASH.range||hd<=2.0+.4*sc||Math.abs(p.y-player.pos.y)>2.2)continue;   // too far / already in slash range / on another level
  const tx=p.x-o.x,ty=p.y+1.2*sc-o.y,tz=p.z-o.z,d=Math.hypot(tx,ty,tz);
  const dot=(tx*dir.x+ty*dir.y+tz*dir.z)/d,need=Math.cos(Math.atan2(sc*.9,d)+.12);   // crosshair on the monster (+ a little aim assist)
  if(dot>need&&dot>bs){bs=dot;best=m;}
 }
 return best;
}
function dashSpark(pos,vel,life,size,col){const p=hfxPut(HFX.sparks,pos,life,size,-size/life*.9,col);p.v.copy(vel);return p;}
function startSwordDash(m,step=0){
 const p=m.root.position,sc=m.cfg.scale,dx=p.x-player.pos.x,dz=p.z-player.pos.z,hd=Math.hypot(dx,dz)||1,nx=dx/hd,nz=dz/hd;
 const stop=1.35+.35*sc,travel=Math.max(0,hd-stop),dur=THREE.MathUtils.clamp(travel/38,.07,.2);
 player.dash={m,t:0,dur,nx,nz,travel,speed:travel/dur,step};
 DASH.cool=.15;DASH.fov=14;DASH.from.copy(player.pos);DASH.dir.set(nx,0,nz);DASH.end.copy(player.pos);DASH.op=.8;
 player.sliding=false;player.jumpBuffer=0;
 try{slamSound('whoosh');}catch(e){}
 if(HFX.ready){
  const c=_dfx.p.set(player.pos.x,player.pos.y+1.0,player.pos.z);
  hfxPut(HFX.flashes,c,.14,2.4,5,0xff4a2a);hfxPut(HFX.rings,c,.24,.5,7,0xff2a1a);
  for(let i=0;i<20;i++){_dfx.v.set((Math.random()-.5)*5-nx*10,Math.random()*3,(Math.random()-.5)*5-nz*10);dashSpark(c,_dfx.v,.22+Math.random()*.2,.14+Math.random()*.14,i%2?0xff3a22:0xffd0b0);}
 }
 slamFx.shake=Math.max(slamFx.shake||0,.18);
}
function dashFinish(){
 const D=player.dash;if(!D)return;player.dash=null;
 player.vel.set(D.nx*2.5,0,D.nz*2.5);DASH.end.copy(player.pos);
 const m=D.m,sc=m.cfg.scale;
 if(HFX.ready&&m.alive){   // impact burst on the monster as the blade comes through
  const c=_dfx.p.set(m.root.position.x-D.nx*.4*sc,m.root.position.y+1.3*sc,m.root.position.z-D.nz*.4*sc);
  hfxPut(HFX.flashes,c,.18,3.2*sc,6,0xffe2b0);hfxPut(HFX.rings,c,.3,.6*sc,8*sc,0xff3a22);
  const a=hfxPut(HFX.arcs,c,.2,3*sc,3,0xff5a3a);a.sx=1.5;a.s.material.rotation=-.6;
  for(let i=0;i<22;i++){const th=Math.random()*6.283,sp=3+Math.random()*7;_dfx.v.set(Math.cos(th)*sp+D.nx*4,Math.random()*5+1,Math.sin(th)*sp+D.nz*4);dashSpark(c,_dfx.v,.25+Math.random()*.25,.12+Math.random()*.12,i%3?0xff3a22:0xffa050).grav=1;}
 }
 slamFx.shake=Math.max(slamFx.shake||0,.3);
 const A=erikaAnim,nm=['SwordSlash','SecondSwordSlash','ThirdSwordSlash'][D.step||0];if(running&&A.ready&&A.attackActs&&A.attackActs[nm]&&!A.attackAction){A.comboStep=D.step||0;A.comboUntil=0;startErikaSwordAttack(nm);}   // the slash (1st, 2nd or 3rd) lands straight away
}
function dashTick(dt){
 const D=player.dash;if(!D)return;
 const ease=u=>u*(2-u),k0=Math.min(1,D.t/D.dur);D.t+=dt;const k1=Math.min(1,D.t/D.dur),step=(ease(k1)-ease(k0))*D.travel;
 const nxp=player.pos.x+D.nx*step,nzp=player.pos.z+D.nz*step;
 let blocked=false;for(const c of colliders){if(c.kind==='roof'||c.kind==='gable'||c.top<.5||c.top<=player.pos.y+.4)continue;if(insideXZ(c,nxp,nzp,.43)){blocked=true;break;}}
 if(!blocked){player.pos.x=nxp;player.pos.z=nzp;}
 player.vel.set(D.nx*D.speed,0,D.nz*D.speed);player.vel.y=0;player.grounded=true;player.airTime=0;player.sliding=false;
 DASH.end.copy(player.pos);
 if(HFX.ready)for(let i=0;i<9;i++){   // speed lines streaming past the runner / camera
  const p=_dfx.p.set(player.pos.x+(Math.random()-.5)*1.8,player.pos.y+.3+Math.random()*1.6,player.pos.z+(Math.random()-.5)*1.8);
  _dfx.v.set(-D.nx*(7+Math.random()*9)+(Math.random()-.5)*1.5,(Math.random()-.5)*1.2,-D.nz*(7+Math.random()*9)+(Math.random()-.5)*1.5);
  dashSpark(p,_dfx.v,.2+Math.random()*.15,.12+Math.random()*.1,i%3===0?0xffe6d6:i%3===1?0xff3a22:0xc01010);
 }
 if(k1>=1||blocked)dashFinish();
}
function dashFxUpdate(dt){
 DASH.cool=Math.max(0,DASH.cool-dt);DASH.fov*=Math.exp(-8*dt);if(DASH.fov<.05)DASH.fov=0;
 dashFxInit();if(!DASH.trail)return;
 if(player.dash)DASH.op=.8;else DASH.op=Math.max(0,DASH.op-dt*3.5);
 const cur=player.dash?player.pos:DASH.end,len=Math.hypot(cur.x-DASH.from.x,cur.z-DASH.from.z),vis=thirdPerson&&DASH.op>.01&&len>.2;
 for(const [m,k] of [[DASH.trail,1],[DASH.core,1.15]]){
  m.visible=vis;if(!vis)continue;
  m.position.set(cur.x,cur.y+1.0,cur.z);m.quaternion.setFromUnitVectors(DASH.up,DASH.dir);m.scale.set(1,len,1);m.material.opacity=DASH.op*(m===DASH.core?.9:.55)*k;
 }
}
// ===================== CHARGED SWORD LUNGE: hold the left mouse button for 1.2 s, then dash forward with a heavy sweeping cut =====================
// A short click is still the normal slash (it now fires when the button is released). Holding the button past LUNGE.delay starts the charge
// (sword pulled back in both hands, red energy gathering, ring around the crosshair); at LUNGE.charge seconds the player coils for an instant and
// then rushes LUNGE.dist metres forward, cutting every monster inside the swept strip.   Tweak live from the console, e.g.  LUNGE.dmg=200  LUNGE.dist=14
const LUNGE={zoomFov:18,charge:.85,delay:.2,wind:.11,dur:.32,recover:.36,dist:15.4,width:3.2,reach:1.9,dmg:93,cool:.6,fov:22,assist:.4,assistRange:16,
 cd:0,pw:0,glow:0,stamp:0,P:{gf:0,gr:0,gu:0,bf:0,br:0,bu:0,tw:0,ln:0},G:new THREE.Vector3(),B:new THREE.Vector3(0,1,0),
 trail:null,samples:[],aura:null,auraMat:null,glows:[],swordMat:null,swordMatI:.9,ring:null,ringOn:false,init:false};
const CHG={down:false,t:0,fired:false,ready:false,air:false};
const _lg={f:new THREE.Vector3(),r:new THREE.Vector3(),u:new THREE.Vector3(0,1,0),chest:new THREE.Vector3(),G:new THREE.Vector3(),B:new THREE.Vector3(),T:new THREE.Vector3(),
 h:new THREE.Vector3(),q:new THREE.Quaternion(),q2:new THREE.Quaternion(),q3:new THREE.Quaternion(),pq:new THREE.Quaternion(),X:new THREE.Vector3(),Z:new THREE.Vector3(),
 v1:new THREE.Vector3(),v2:new THREE.Vector3(),m:new THREE.Matrix4(),tip:new THREE.Vector3(),base:new THREE.Vector3(),fx:new THREE.Vector3(),fv:new THREE.Vector3()};
// pose keys, in the body frame:  [grip fwd, grip right, grip up (from the chest),  blade fwd, blade right, blade up,  torso twist (rad, + = to the left), torso lean (rad, - = forward)]
const LG_READY=[-.10,.30,-.40,  .78,.22,-.25,  -.35,-.16];   // sword drawn back on the right hip, blade pointing forward along the side
const LG_WIND =[-.30,.44,-.20, -.25,.85,.28,   -.85,-.24];   // coil: sword swung out to the right and back, shoulders turned away
const LG_GUARD=[.30,-.15,-.35,  .60,-.45,.15,   .20,-.20];   // follow-through: low guard on the left
const LG_AIRHOLD=[-.30,.44,-.20,  -.25,.85,.28,  0,0];   // same grip as the ground strike's coil pose: sword out to the right in both hands, torso untouched
const LG_AIRFWD=[.36,.08,-.20,  1,0,.05,  0,0];   // air strike itself: both hands thrust the sword straight ahead
const LG_A0=1.95,LG_A1=-1.55;                                // blade sweep angle (from forward toward the right): from right-back, across the front, to the left
const lgMix=(a,b,k,o)=>{for(let i=0;i<8;i++)o[i]=a[i]+(b[i]-a[i])*k;return o;};
const _lgA=new Array(8).fill(0),_lgB=new Array(8).fill(0);
function lgSweepKey(u,o){   // u 0..1 across the dash: a fast, heavy cut that decelerates into the follow-through
 const e=1-Math.pow(1-u,2.6),a=LG_A0+(LG_A1-LG_A0)*e,reach=.30+.30*Math.sin(Math.min(1,u*1.25)*Math.PI*.9),ga=a*.75;
 o[0]=Math.cos(ga)*reach;o[1]=Math.sin(ga)*reach;o[2]=-.16-.04*Math.sin(u*Math.PI);
 o[3]=Math.cos(a);o[4]=Math.sin(a);o[5]=.10;
 o[6]=-.85+1.7*e;o[7]=-.50;return o;
}
function lungePose(P){
 const L=player.lunge,o=_lgA,chg=CHG.down&&CHG.t>LUNGE.delay;
 if(L)LUNGE.la=!!L.air;else if(chg)LUNGE.la=!player.grounded;
 if(!L&&!chg){for(let i=0;i<8;i++)o[i]=LG_GUARD[i];}   // fading out after the strike: hold the follow-through guard (no jump back to the old charge pose)
 else if(!L){   // charging: ready stance, tightening and trembling as the energy builds
  const p=THREE.MathUtils.clamp((CHG.t-LUNGE.delay)/(LUNGE.charge-LUNGE.delay),0,1);
  lgMix(LG_READY,LG_WIND,p*.35,o);const sh=Math.sin(CHG.t*70)*.004*p;o[0]+=sh;o[2]+=Math.sin(CHG.t*53)*.005*p;
 }else if(L.phase==='wind'){const u=Math.min(1,L.t/LUNGE.wind);lgMix(LG_READY,LG_WIND,.35+.65*(1-(1-u)*(1-u)),o);}   // starts exactly where the charge pose ended: no snap
 else if(L.phase==='dash'){lgSweepKey(Math.min(1,L.u||0),o);}
 else{const u=Math.min(1,L.t/LUNGE.recover),e=u*u*(3-2*u);lgSweepKey(1,_lgB);lgMix(_lgB,LG_GUARD,e,o);}
 if(LUNGE.la){const k=L?(L.phase==='wind'?(u=>u*u*(3-2*u))(Math.min(1,L.t/LUNGE.wind)):1):(chg?0:1);lgMix(LG_AIRHOLD,LG_AIRFWD,k,o);}   // air: sword out to the right while charging, then swung straight forward for the strike   // air strike: one fixed pose from start to finish, no sweep, no torso twist   // in the air the torso twist is halved and the body pitch (lungeLeanApply) replaces the forward lean
 P.gf=o[0];P.gr=o[1];P.gu=o[2];P.bf=o[3];P.br=o[4];P.bu=o[5];P.tw=o[6];P.ln=o[7];return P;
}
// ===================== BLOCK (Q): half a second of guarding. Monster hits do no damage; the player cannot move, attack or do anything else meanwhile =====================
const BLOCK={dur:.5,cool:.35,cd:0,flash:0,g:null,ring:null,disc:null,dome:null,ringMat:null,discMat:null,domeMat:null};
function blockCan(){
 const A=erikaAnim;
 return running&&mouse.locked&&!playerDeath.active&&!player.block&&!rollLocked()&&BLOCK.cd<=0&&player.grounded&&!player.slam&&!player.dash&&!player.lunge&&!player.kick&&!player.climbing&&!player.onWall&&!player.sliding&&!player.mantle&&!player.postFlight&&!(grapplePull&&grapplePull.active)&&monsterRespawnTimer<=0&&!SUPER.aim&&!!A&&A.ready&&!!A.blockAct;
}
function blockStart(){
 if(!blockCan())return;
 lungeHoldCancel();try{stopAim();cancelBowDraw();if(bow.nocked)bow.nocked.visible=false;}catch(e){}   // guarding: the nocked arrow disappears from the hand
 const A=erikaAnim;   // a slash in progress is cut short
 if(A.attackAction){for(const a of Object.values(A.attackActs))a.stop();for(const a of Object.values(A.attackUpper))a.stop();A.attackAction=null;A.atkFull=null;A.atkUpper=null;A.atkPrev=null;A.atkPrevUp=null;A.attackWeight=0;A.attackTarget=0;A.attackMove=0;A.comboStep=-1;A.comboUntil=0;}
 player.block={t:0,started:false};BLOCK.cd=BLOCK.dur+BLOCK.cool;BLOCK.flash=0;player.sliding=false;player.jumpBuffer=0;
 try{sound('block');}catch(e){}
 if(HFX.ready)hfxPut(HFX.rings,_lg.fv.set(player.pos.x,player.pos.y+.12,player.pos.z),.3,.6,9,0x2f7dff);
}
function blockMove(dt){   // replaces resolveMovement: the player stays rooted
 const B=player.block;if(!B)return;
 B.t+=dt;player.grounded=true;player.airTime=0;player.sliding=false;player.jumpBuffer=0;player.vel.set(0,0,0);
 if(B.t>=BLOCK.dur)player.block=null;
}
function blockHit(src){   // a monster blow (or spit) lands on the guard: no damage, light-blue sparks and a small shake
 BLOCK.flash=1;slamFx.shake=Math.max(slamFx.shake||0,.18);try{sound('swordHit');}catch(e){}
 if(HFX.ready){
  const c=_lg.fx.set(player.pos.x,player.pos.y+1.1,player.pos.z);
  if(src){const dx=src.x-player.pos.x,dz=src.z-player.pos.z,l=Math.hypot(dx,dz)||1;c.x+=dx/l*.7;c.z+=dz/l*.7;}
  hfxPut(HFX.flashes,c,.16,2.2,5,0x4d8fff);
  for(let i=0;i<16;i++){const th=Math.random()*6.283,sp=3+Math.random()*6;_dfx.v.set(Math.cos(th)*sp,Math.random()*4,Math.sin(th)*sp);const q=dashSpark(c,_dfx.v,.25+Math.random()*.25,.1+Math.random()*.1,i%2?0x2f7dff:0x7fb0ff);q.grav=.4;}
 }
}
function blockFxUpdate(dt){
 BLOCK.flash=Math.max(0,BLOCK.flash-dt*4);
 if(!BLOCK.g){
  if(!scene)return;
  const mk=c=>new THREE.MeshBasicMaterial({color:c,transparent:true,opacity:0,depthWrite:false,blending:THREE.AdditiveBlending,side:THREE.DoubleSide,fog:false});
  BLOCK.ringMat=mk(0x2f7dff);BLOCK.discMat=mk(0x1e5cff);BLOCK.domeMat=mk(0x2468ff);
  const g=new THREE.Group();g.visible=false;
  const ring=new THREE.Mesh(new THREE.RingGeometry(.93,1,72),BLOCK.ringMat),disc=new THREE.Mesh(new THREE.CircleGeometry(.93,56),BLOCK.discMat),dome=new THREE.Mesh(new THREE.SphereGeometry(1,28,18),BLOCK.domeMat);
  ring.rotation.x=disc.rotation.x=-Math.PI/2;ring.position.y=disc.position.y=.07;disc.position.y=.06;dome.position.y=.9;
  for(const o of [ring,disc,dome]){o.frustumCulled=false;o.renderOrder=16;g.add(o);}
  scene.add(g);BLOCK.g=g;BLOCK.ring=ring;BLOCK.disc=disc;BLOCK.dome=dome;
 }
 const B=player.block;
 if(!B){BLOCK.g.visible=false;return;}
 const sm=(a,b,x)=>{const t=Math.min(1,Math.max(0,(x-a)/(b-a)));return t*t*(3-2*t);};
 const pop=sm(0,.1,B.t),fade=1-sm(BLOCK.dur-.12,BLOCK.dur,B.t),k=pop*fade,f=BLOCK.flash;
 BLOCK.g.visible=true;BLOCK.g.position.set(player.pos.x,player.pos.y,player.pos.z);
 const R=1.45*(.55+.45*pop)*(1+.05*f);
 BLOCK.ring.scale.set(R,R,1);BLOCK.disc.scale.set(R,R,1);BLOCK.dome.scale.set(R*.82,R*.95,R*.82);
 BLOCK.ringMat.opacity=Math.min(1,(.85+.15*f)*k);BLOCK.discMat.opacity=(.16+.2*f)*k;
 BLOCK.dome.visible=thirdPerson;BLOCK.domeMat.opacity=(.1+.2*f)*k;
}
// ===================== LEVELS: killing monsters gives XP; every level needs more XP than the one before =====================
// XP needed to go from level L to L+1 = XPSYS.base * L^XPSYS.pow  (100, 255, 468, ...).  Tweak live: XPSYS.base=80  XPSYS.xp.brute=80
const XPSYS={level:1,base:100,pow:1.35,xp:{stalker:20,spitter:30,brute:50},cur:0,shown:'',pulse:0,decay:.03,floor:.3,kills:0,maxDry:1,dry:0};   // maxDry: most waves in a row you can clear WITHOUT levelling up (1 = the 2nd wave always gives a level; 0 = a level every wave)
function xpNeed(L){return Math.round(XPSYS.base*Math.pow(L,XPSYS.pow));}
function xpFullLevel(){   // boss reward: +1 full level, keeping the same fill of the bar (end of level 3 -> end of level 4)
 const f=Math.min(.999,XPSYS.cur/Math.max(1,xpNeed(XPSYS.level)));XPSYS.level++;XPSYS.dry=0;UP.points++;XPSYS.cur=Math.floor(f*xpNeed(XPSYS.level));XPSYS.pulse=1;try{levelUpFx();}catch(e){}
}
function xpWaveCheck(){   // called when a wave is cleared: never allow more than XPSYS.maxDry waves in a row without a level-up
 if(XPSYS.dry<XPSYS.maxDry){XPSYS.dry++;return;}
 XPSYS.cur=Math.max(XPSYS.cur,xpNeed(XPSYS.level));
 while(XPSYS.cur>=xpNeed(XPSYS.level)){XPSYS.cur-=xpNeed(XPSYS.level);XPSYS.level++;XPSYS.dry=0;UP.points++;XPSYS.pulse=1;try{levelUpFx();}catch(e){}}
}
function xpGain(m){
 XPSYS.kills=(XPSYS.kills||0)+1;const _xm=Math.max(XPSYS.floor,Math.pow(1-XPSYS.decay,XPSYS.kills-1));   // each kill pays XPSYS.decay (3%) less than the one before, never below XPSYS.floor of the base reward
 XPSYS.cur+=Math.max(1,Math.round((XPSYS.xp[m.type]||25)*_xm));
 while(XPSYS.cur>=xpNeed(XPSYS.level)){XPSYS.cur-=xpNeed(XPSYS.level);XPSYS.level++;XPSYS.dry=0;UP.points++;XPSYS.pulse=1;try{levelUpFx();}catch(e){}}
}
// ---- LEVEL-UP WALL: a soft, translucent cylinder of rising chevrons + "LEVEL UP" text around the player for LVWALL.dur seconds ----
const LVWALL={dur:1,radius:.55,height:2.5,mesh:null,ring:null,tex:null,t:-1,col:0x5fa8ff};
function lvWallBuild(){
 const c=document.createElement('canvas');c.width=512;c.height=720;const g=c.getContext('2d');
 const grd=g.createLinearGradient(0,0,0,720);grd.addColorStop(0,'rgba(95,168,255,0)');grd.addColorStop(.5,'rgba(95,168,255,.28)');grd.addColorStop(1,'rgba(95,168,255,.05)');g.fillStyle=grd;g.fillRect(0,0,512,720);
 g.strokeStyle='rgba(190,226,255,.9)';g.lineWidth=5;g.shadowColor='#7fc0ff';g.shadowBlur=18;
 for(let k=0;k<2;k++){const y=95+k*530;g.beginPath();g.moveTo(0,y);g.lineTo(512,y);g.stroke();}
 g.textAlign='center';g.textBaseline='middle';g.fillStyle='#eaf6ff';g.font='800 76px sans-serif';g.fillText('LEVEL UP',256,330);
 g.font='700 56px sans-serif';g.fillText('\u25B2 \u25B2 \u25B2',256,440);
 g.lineWidth=4;for(let i=0;i<4;i++){const x=64+i*128;g.beginPath();g.moveTo(x-22,600);g.lineTo(x,572);g.lineTo(x+22,600);g.stroke();g.beginPath();g.moveTo(x-22,170);g.lineTo(x,142);g.lineTo(x+22,170);g.stroke();}
 const tex=new THREE.CanvasTexture(c);tex.wrapS=THREE.RepeatWrapping;tex.wrapT=THREE.RepeatWrapping;tex.repeat.set(2,1);if(THREE.SRGBColorSpace)tex.colorSpace=THREE.SRGBColorSpace;LVWALL.tex=tex;
 const geo=new THREE.CylinderGeometry(LVWALL.radius,LVWALL.radius,LVWALL.height,64,1,true);
 const mat=new THREE.MeshBasicMaterial({map:tex,transparent:true,opacity:0,side:THREE.DoubleSide,depthWrite:false,blending:THREE.AdditiveBlending,fog:false});
 const m=new THREE.Mesh(geo,mat);m.visible=false;m.renderOrder=20;m.frustumCulled=false;scene.add(m);LVWALL.mesh=m;
 const rm=new THREE.MeshBasicMaterial({color:0xbfe2ff,transparent:true,opacity:0,side:THREE.DoubleSide,depthWrite:false,blending:THREE.AdditiveBlending,fog:false});
 const r=new THREE.Mesh(new THREE.RingGeometry(LVWALL.radius*.9,LVWALL.radius*1.03,64),rm);r.rotation.x=-Math.PI/2;r.visible=false;r.renderOrder=21;r.frustumCulled=false;scene.add(r);LVWALL.ring=r;
}
function lvWallStart(){try{if(!LVWALL.mesh)lvWallBuild();LVWALL.t=0;LVWALL.mesh.visible=true;LVWALL.ring.visible=true;}catch(e){console.error('[level wall]',e);}}
function lvWallUpdate(dt){
 if(LVWALL.t<0||!LVWALL.mesh)return;
 LVWALL.t+=dt;const u=LVWALL.t/LVWALL.dur;
 if(u>=1){LVWALL.t=-1;LVWALL.mesh.visible=false;LVWALL.ring.visible=false;return;}
 const ss=x=>x*x*(3-2*x),fade=ss(Math.min(1,u/.18))*(1-ss(Math.max(0,(u-.5)/.5)));
 const grow=1-Math.pow(1-Math.min(1,u/.4),3),sc=.55+.45*grow;
 const m=LVWALL.mesh,H=LVWALL.height;
 m.position.set(player.pos.x,player.pos.y+H*.5-.1,player.pos.z);m.scale.set(sc,1,sc);m.rotation.y+=dt*1.6;
 m.material.opacity=.7*fade;LVWALL.tex.offset.y=-u*.5;
 const r=LVWALL.ring;r.position.set(player.pos.x,player.pos.y+.05+u*(H-.2),player.pos.z);r.scale.set(sc,sc,1);r.material.opacity=.9*fade;
}
function levelUpFx(){
 slamFx.shake=Math.max(slamFx.shake||0,.12);lvWallStart();try{sound('levelup');}catch(e){}
 if(HFX.ready){const c=_lg.fx.set(player.pos.x,player.pos.y+1.1,player.pos.z);hfxPut(HFX.flashes,c,.3,3,5,0x5fa8ff);hfxPut(HFX.rings,_lg.fv.set(player.pos.x,player.pos.y+.12,player.pos.z),.5,.6,12,0x5fa8ff);
  for(let i=0;i<30;i++){_dfx.v.set((Math.random()-.5)*6,2+Math.random()*6,(Math.random()-.5)*6);dashSpark(c,_dfx.v,.5+Math.random()*.4,.12+Math.random()*.12,i%2?0x5fa8ff:0xcfe6ff).grav=.3;}}
}
function xpHud(dt){
 XPSYS.pulse=Math.max(0,XPSYS.pulse-dt*1.5);
 const box=document.getElementById('monsterHUD');if(!box)return;
 const f=box.querySelector('.lv-fill'),n=box.querySelector('.lv-num');if(!f||!n)return;
 const need=xpNeed(XPSYS.level),key=XPSYS.level+'|'+XPSYS.cur+'|'+(XPSYS.pulse>0);if(key===XPSYS.shown)return;XPSYS.shown=key;
 n.textContent=XPSYS.level;f.style.width=Math.min(100,XPSYS.cur/need*100).toFixed(1)+'%';f.style.filter=XPSYS.pulse>0?'brightness(1.8)':'';
}
// ===================== UPGRADES (P, between waves): every level gained = 1 point to spend =====================
// Tweak live: UPG.defs.health.per=30   UPG.defs.stamina.max=4
const UP={points:0,maxHp:100,swordMul:1,bowMul:1,prev:{sword:null,bow:null},rank:{stamina:0,health:0,super:0,sword:0,bow:0}};
const UPG={open:false,el:null,hint:null,defs:{
 stamina:{name:'STAMINA CAPACITY',max:3,desc:r=>'Strong attacks use one segment each. Segments: '+(2+r)+(r<3?' → '+(3+r):' (MAX)'),icon:'&#9889;'},
 health:{name:'VITALITY',max:5,per:20,desc:r=>'Maximum health: '+(100+20*r)+(r<5?' → '+(120+20*r):' (MAX)'),icon:'&#9829;'},
 sword:{name:'SWORD DAMAGE',max:5,per:.15,desc:r=>'Sword damage: +'+Math.round(15*r)+'%'+(r<5?' → +'+Math.round(15*(r+1))+'%':' (MAX)'),icon:'&#128481;'},
 bow:{name:'ARROW DAMAGE',max:5,per:.15,desc:r=>'Arrow damage: +'+Math.round(15*r)+'%'+(r<5?' → +'+Math.round(15*(r+1))+'%':' (MAX)'),icon:'&#10146;'},
 super:{name:'SUPER STRIKE',max:3,per:5,desc:r=>'Kills needed to charge the super strike: '+(25-5*r)+(r<3?' → '+(20-5*r):' (MAX)'),icon:'&#9876;'}}};
// ---- BALANCE: tweak live (e.g. BAL.hpPerWave=.2).  Monster HP and damage grow with the wave; arrows now hit hard but no longer one-shot everything ----
const BAL={hpPerWave:.10,hpCap:4,dmgPerWave:.035,dmgCap:1.8,arrowBase:80,arrowPow:130,
 hpMul(n){return Math.min(this.hpCap,1+this.hpPerWave*(n-1));},dmgMul(n){return Math.min(this.dmgCap,1+this.dmgPerWave*((n||WAVES.n)-1));}};
function balApplyHp(m){m.maxHp=Math.round(m.cfg.hp*BAL.hpMul(WAVES.n));m.hp=m.maxHp;}

// ===================== TAB STATS PANEL: hold TAB to see monster HP / damage and the sword + arrow damage (current / previous / after the next upgrade) =====================
const TABP={el:null,down:false,base:{brute:{name:'ASHEN BRUTE',hp:230,dmg:24},stalker:{name:'NIGHT STALKER',hp:105,dmg:13},spitter:{name:'MIRE SPITTER',hp:145,dmg:17}}};
function tabBuild(){
 if(TABP.el)return;
 const st=document.createElement('style');
 st.textContent='#tabPanel{position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);z-index:55;display:none;width:min(720px,94vw);padding:22px 26px;border-radius:14px;background:linear-gradient(200deg,rgba(24,28,40,.94),rgba(10,12,18,.94));border:1px solid rgba(255,255,255,.14);box-shadow:0 20px 60px rgba(0,0,0,.6);font-family:var(--ui,sans-serif);color:#eee;pointer-events:none;letter-spacing:.08em}#tabPanel.show{display:block}#tabPanel h3{margin:0 0 8px;font-size:13px;letter-spacing:.2em;color:var(--gold,#f0c46e)}#tabPanel h3:not(:first-child){margin-top:18px}#tabPanel table{width:100%;border-collapse:collapse;font-size:13px}#tabPanel th{font-size:11px;color:#9a9890;font-weight:700;text-align:right;padding:4px 8px}#tabPanel th:first-child,#tabPanel td:first-child{text-align:left}#tabPanel td{padding:6px 8px;text-align:right;border-top:1px solid rgba(255,255,255,.07)}#tabPanel td b{color:#fff}#tabPanel .up{color:#7fe3a0}#tabPanel .dim{color:#8a8880}#tabPanel .wv{float:right;font-size:11px;color:#9a9890;letter-spacing:.14em}';
 document.head.appendChild(st);
 const el=document.createElement('div');el.id='tabPanel';document.body.appendChild(el);TABP.el=el;
}
function tabRender(){
 const n=WAVES.n,hm=BAL.hpMul(n),dm=BAL.dmgMul(n),R=UP.rank,mx=UPG.defs.sword.max;
 let h='<h3>MONSTERS <span class="wv">WAVE '+n+' &nbsp;·&nbsp; HP ×'+hm.toFixed(2)+' &nbsp;·&nbsp; DAMAGE ×'+dm.toFixed(2)+'</span></h3><table><tr><th></th><th>HEALTH</th><th>DAMAGE</th></tr>';
 for(const k in TABP.base){const b=TABP.base[k];h+='<tr><td>'+b.name+'</td><td><b>'+Math.round(b.hp*hm)+'</b></td><td><b>'+(b.dmg*dm).toFixed(1)+'</b></td></tr>';}
 h+='</table>';
 const row=(name,base,cur,prev,next)=>'<tr><td>'+name+'</td><td><b>'+Math.round(base*cur*hm)+'</b></td><td class="dim">'+(prev==null?'—':Math.round(base*prev*hm))+'</td><td class="up">'+(next==null?'MAX':Math.round(base*next*hm))+'</td></tr>';
 const sNext=R.sword<mx?1+UPG.defs.sword.per*(R.sword+1):null,bNext=R.bow<UPG.defs.bow.max?1+UPG.defs.bow.per*(R.bow+1):null;
 h+='<h3>SWORD DAMAGE <span class="wv">WAVE ×'+hm.toFixed(2)+' &nbsp;·&nbsp; UPGRADE +'+Math.round((UP.swordMul-1)*100)+'%</span></h3><table><tr><th></th><th>CURRENT</th><th>PREVIOUS</th><th>AFTER UPGRADE</th></tr>'
  +row('1st slash',58,UP.swordMul,UP.prev.sword,sNext)+row('2nd slash',74,UP.swordMul,UP.prev.sword,sNext)+row('3rd slash',103,UP.swordMul,UP.prev.sword,sNext)
  +row('Charged lunge',LUNGE.dmg,UP.swordMul,UP.prev.sword,sNext)+row('Leap strike',JSTRIKE.dmg,UP.swordMul,UP.prev.sword,sNext)+'</table>';
 h+='<h3>ARROW DAMAGE <span class="wv">WAVE ×'+hm.toFixed(2)+' &nbsp;·&nbsp; UPGRADE +'+Math.round((UP.bowMul-1)*100)+'%</span></h3><table><tr><th></th><th>CURRENT</th><th>PREVIOUS</th><th>AFTER UPGRADE</th></tr>'
  +row('Arrow (full draw only)',BAL.arrowBase+BAL.arrowPow,UP.bowMul,UP.prev.bow,bNext)+'</table>';
 TABP.el.innerHTML=h;
}
function tabShow(v){
 if(v&&!(running&&!UPG.open&&!playerDeath.active))return;
 tabBuild();TABP.down=v;if(v)tabRender();TABP.el.classList.toggle('show',v);
}
window.addEventListener('keydown',e=>{if(e.code==='Tab'){e.preventDefault();if(!e.repeat)tabShow(true);else if(TABP.down)tabRender();}},true);
window.addEventListener('keyup',e=>{if(e.code==='Tab'){e.preventDefault();tabShow(false);}},true);
window.addEventListener('blur',()=>{if(TABP.el)tabShow(false);});
function upgApply(){
 STAM.max=2+UP.rank.stamina;STAM.cur=Math.min(STAM.cur,STAM.max);if(STAM.cur<STAM.max&&STAM.timer<=0)STAM.timer=STAM.regen;
 if(STAM.el){STAM.el.remove();STAM.el=null;STAM.segs=[];STAM.last='';}
 UP.maxHp=100+UPG.defs.health.per*UP.rank.health;UP.swordMul=1+UPG.defs.sword.per*UP.rank.sword;UP.bowMul=1+UPG.defs.bow.per*UP.rank.bow;
 SUPER.need=Math.max(5,25-UPG.defs.super.per*UP.rank.super);if(SUPER.kills>SUPER.need)SUPER.kills=SUPER.need;
}
function upgReset(){UP.points=0;UP.rank.stamina=UP.rank.health=UP.rank.super=UP.rank.sword=UP.rank.bow=0;UP.prev.sword=UP.prev.bow=null;upgApply();STAM.cur=STAM.max;STAM.timer=0;if(UPG.open)upgClose(true);}
function upgBuy(k){
 const d=UPG.defs[k];if(UP.points<1||UP.rank[k]>=d.max)return;
 UP.points--;if(k==='sword')UP.prev.sword=UP.swordMul;if(k==='bow')UP.prev.bow=UP.bowMul;UP.rank[k]++;upgApply();
 if(k==='stamina'){STAM.cur=Math.min(STAM.max,STAM.cur+1);}
 if(k==='health'){playerHealth=Math.min(UP.maxHp,playerHealth+UPG.defs.health.per);updateMonsterHUD();}
 try{sound('upgrade');}catch(e){}
 upgRender();
}
function upgRender(){
 if(!UPG.el)return;
 UPG.el.querySelector('.up-pts').textContent=UP.points;
 for(const k in UPG.defs){const d=UPG.defs[k],r=UP.rank[k],card=UPG.el.querySelector('[data-k="'+k+'"]');
  card.querySelector('.up-desc').textContent=d.desc(r);
  card.querySelector('.up-pips').innerHTML=Array.from({length:d.max},(_,i)=>'<i class="'+(i<r?'on':'')+'"></i>').join('');
  const b=card.querySelector('button');b.disabled=UP.points<1||r>=d.max;b.textContent=r>=d.max?'MAXED':'UPGRADE  (1 pt)';}
}
function upgBuild(){
 if(UPG.el)return;
 const st=document.createElement('style');
 st.textContent='#upgMenu{position:fixed;inset:0;z-index:60;display:none;align-items:center;justify-content:center;background:rgba(4,6,10,.78);backdrop-filter:blur(5px);font-family:var(--ui,sans-serif);color:#eee}#upgMenu.show{display:flex}#upgMenu .up-panel{width:min(760px,92vw);padding:26px 28px;border-radius:14px;background:linear-gradient(200deg,rgba(24,28,40,.96),rgba(10,12,18,.96));border:1px solid rgba(255,255,255,.12);box-shadow:0 20px 60px rgba(0,0,0,.6)}#upgMenu h2{margin:0;font-size:28px;letter-spacing:.2em}#upgMenu .up-sub{margin:6px 0 20px;font-size:13px;letter-spacing:.12em;color:#9fb7d8}#upgMenu .up-sub b{color:#7fc0ff;font-size:18px}#upgMenu .up-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:14px}#upgMenu .up-card{padding:16px 14px;border-radius:10px;background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.1);display:flex;flex-direction:column;gap:10px}#upgMenu .up-ico{font-size:26px;color:#7fc0ff}#upgMenu .up-name{font-weight:800;letter-spacing:.14em;font-size:13px}#upgMenu .up-desc{font-size:12px;line-height:1.5;color:#c9d3e2;min-height:54px}#upgMenu .up-pips{display:flex;gap:5px}#upgMenu .up-pips i{width:18px;height:6px;border-radius:3px;background:rgba(255,255,255,.14)}#upgMenu .up-pips i.on{background:linear-gradient(90deg,#2f6dff,#7fc0ff);box-shadow:0 0 8px rgba(80,150,255,.7)}#upgMenu button{padding:9px 10px;border-radius:8px;border:1px solid rgba(127,192,255,.5);background:rgba(47,109,255,.25);color:#fff;font-weight:700;letter-spacing:.1em;cursor:pointer}#upgMenu button:hover:not(:disabled){background:rgba(47,109,255,.5)}#upgMenu button:disabled{opacity:.4;cursor:default}#upgMenu .up-close{margin-top:18px;width:100%}#upgHint{position:fixed;left:50%;top:98px;transform:translateX(-50%);z-index:31;display:none;padding:14px 34px;border-radius:999px;background:linear-gradient(180deg,rgba(14,26,48,.9),rgba(8,14,26,.88));border:2px solid rgba(127,192,255,.85);color:#e4f2ff;font-size:28px;font-weight:800;letter-spacing:.16em;white-space:nowrap;text-shadow:0 0 14px rgba(120,190,255,.9);box-shadow:0 0 28px rgba(95,168,255,.55),0 8px 28px rgba(0,0,0,.5);pointer-events:none;animation:upgHintPulse 1.1s ease-in-out infinite}@keyframes upgHintPulse{0%,100%{transform:translateX(-50%) scale(1);box-shadow:0 0 22px rgba(95,168,255,.45),0 8px 28px rgba(0,0,0,.5)}50%{transform:translateX(-50%) scale(1.07);box-shadow:0 0 44px rgba(95,168,255,.9),0 8px 28px rgba(0,0,0,.5)}}@media(max-width:700px){#upgMenu .up-grid{grid-template-columns:1fr}}';
 document.head.appendChild(st);
 const el=document.createElement('div');el.id='upgMenu';
 el.innerHTML='<div class="up-panel"><h2>UPGRADES</h2><div class="up-sub">POINTS TO SPEND <b class="up-pts">0</b> &nbsp;·&nbsp; EVERY LEVEL GIVES 1 POINT</div><div class="up-grid">'+Object.keys(UPG.defs).map(k=>'<div class="up-card" data-k="'+k+'"><div class="up-ico">'+UPG.defs[k].icon+'</div><div class="up-name">'+UPG.defs[k].name+'</div><div class="up-desc"></div><div class="up-pips"></div><button type="button"></button></div>').join('')+'</div><button type="button" class="up-close">CONTINUE  (P)</button></div>';
 document.body.appendChild(el);UPG.el=el;
 el.querySelectorAll('.up-card').forEach(c=>c.querySelector('button').onclick=()=>upgBuy(c.dataset.k));
 el.querySelector('.up-close').onclick=()=>upgClose();
 const h=document.createElement('div');h.id='upgHint';document.body.appendChild(h);UPG.hint=h;
}
function upgCanOpen(){return started&&running&&!paused&&!playerDeath.active&&WAVES.state==='break'&&!UPG.open;}
function upgOpen(){
 upgBuild();upgRender();UPG.open=true;UPG.el.classList.add('show');
 running=false;paused=true;try{stopRunFootsteps();}catch(e){}if(document.pointerLockElement)document.exitPointerLock();
}
function upgClose(silent){
 if(!UPG.open)return;UPG.open=false;if(UPG.el)UPG.el.classList.remove('show');
 if(!silent){running=true;paused=false;renderer.domElement.requestPointerLock?.();}
}
function upgToggle(){if(UPG.open)upgClose();else if(upgCanOpen())upgOpen();}
function upgHintUpdate(){
 if(!UPG.hint){if(!started)return;upgBuild();}
 const show=running&&!UPG.open&&WAVES.state==='break'&&!playerDeath.active;
 UPG.hint.style.display=show?'block':'none';
 if(show)UPG.hint.textContent='P — UPGRADES'+(UP.points>0?'  ('+UP.points+' POINT'+(UP.points>1?'S':'')+')':'');
}
// ===================== STAMINA: 2 segments; every strong attack (leap strike, ground slam from the air, charged lunge) uses one =====================
// A spent segment comes back STAM.regen seconds later, then the next one STAM.regen seconds after that. With 0 segments no strong attack can be used.
const STAM={max:2,cur:2,timer:0,regen:4,flash:0,el:null,segs:[],last:''};
function stamCan(){return STAM.cur>=1;}
function stamSpend(){if(STAM.cur<=0)return false;if(STAM.cur>=STAM.max)STAM.timer=STAM.regen;STAM.cur--;return true;}
function stamDeny(){STAM.flash=.5;}
function stamReset(){STAM.cur=STAM.max;STAM.timer=0;STAM.flash=0;}
function stamUpdate(dt){
 STAM.flash=Math.max(0,STAM.flash-dt);
 if(STAM.cur<STAM.max){STAM.timer-=dt;if(STAM.timer<=0){STAM.cur++;STAM.timer=STAM.cur<STAM.max?STAM.regen:0;}}
}
function breakTimerUpdate(){
 let bt=document.getElementById('breakTimer');
 if(!bt){bt=document.createElement('div');bt.id='breakTimer';bt.style.cssText='position:fixed;left:50%;bottom:58px;transform:translateX(-50%);z-index:4;pointer-events:none;text-align:center;font-family:var(--ui,sans-serif);color:#ffe9b0;text-shadow:0 0 14px rgba(240,196,110,.55),0 2px 6px #000;display:none;white-space:nowrap;';(document.getElementById('screen')||document.body).appendChild(bt);}
 const on=running&&WAVES.state==='break'&&!playerDeath.active&&!UPG.open,tt=Math.ceil(Math.max(0,WAVES.breakT)),kk=on?String(tt):'';
 if(bt._k!==kk){bt._k=kk;bt.style.display=on?'block':'none';if(on)bt.innerHTML='<div style="font-size:11px;letter-spacing:.3em;opacity:.85">NEXT WAVE IN</div><div style="font-size:40px;font-weight:700;line-height:1">'+tt+'<span style="font-size:18px">s</span></div>';}
}
function stamHud(){
 breakTimerUpdate();
 if(!STAM.el){
  const el=document.createElement('div');el.id='stamBar';
  el.style.cssText='position:fixed;left:50%;bottom:34px;transform:translateX(-50%);display:flex;gap:6px;pointer-events:none;z-index:3;';
  for(let i=0;i<STAM.max;i++){const seg=document.createElement('div');seg.style.cssText='position:relative;width:112px;height:11px;background:rgba(0,0,0,.55);border:1px solid rgba(255,255,255,.28);transform:skewX(-18deg);overflow:hidden;';
   const f=document.createElement('i');f.style.cssText='position:absolute;left:0;top:0;bottom:0;width:0;background:linear-gradient(90deg,#ff7a2a,#ffd27a);box-shadow:0 0 8px rgba(255,140,50,.8);';seg.appendChild(f);el.appendChild(seg);STAM.segs.push({seg,f});}
  const host=document.getElementById('screen')||document.body;host.appendChild(el);STAM.el=el;
 }
 const prog=STAM.cur<STAM.max?1-Math.max(0,STAM.timer)/STAM.regen:0,key=STAM.cur+'|'+prog.toFixed(2)+'|'+(STAM.flash>0);if(key===STAM.last)return;STAM.last=key;
 for(let i=0;i<STAM.max;i++){const S=STAM.segs[i],full=i<STAM.cur,part=i===STAM.cur;S.f.style.width=(full?100:part?prog*100:0)+'%';S.f.style.opacity=full?'1':'.55';
  S.seg.style.borderColor=STAM.flash>0&&!full?'rgba(255,60,40,.95)':'rgba(255,255,255,.28)';}
}
function lungeCan(){
 const A=erikaAnim;
 return running&&mouse.locked&&!playerDeath.active&&weapon==='sword'&&!player.slam&&!player.dash&&!player.kick&&!player.lunge&&!player.climbing&&!player.onWall&&!player.sliding&&!player.mantle&&!(grapplePull&&grapplePull.active)&&monsterRespawnTimer<=0&&LUNGE.cd<=0&&!SUPER.aim&&stamCan()&&!!A&&A.ready&&(!A.attackAction||A.comboStep>=1);
}
function lungeHoldBegin(){   // mouse down: true = the click is held back (tap -> slash on release, hold -> charge)
 if(!lungeCan())return false;
 CHG.down=true;CHG.t=0;CHG.fired=false;CHG.ready=false;CHG.air=!player.grounded;return true;   // CHG.air: charged while jumping -> the player hovers until the charge is full
}
function lungeHoldRelease(){
 if(!CHG.down)return;CHG.down=false;
 if(CHG.ready){CHG.ready=false;CHG.fired=true;if(running&&mouse.locked&&!playerDeath.active&&!player.lunge)startLunge();return;}   // fully charged: the lunge goes off when the button is let go
 if(!CHG.fired&&running&&mouse.locked&&!playerDeath.active){if(!player.grounded)airStrikeTap();else triggerSwordSlash();}   // released before the charge was full: an ordinary slash (in the air: the leap strike / ground slam)
}
function airStrikeTap(){if(stamCan()){const had=!!player.slam;if(!(player.gJump&&startJumpStrike()))startGroundSlam();if(player.slam&&!had)stamSpend();}else stamDeny();}
function lungeAirHold(dt){player.vel.set(0,0,0);player.grounded=false;player.onWall=false;player.sliding=false;}   // replaces resolveMovement while an AIR charge is held: no gravity, the player stays where they are
function lungeFloorY(x,z,y){let f=0;for(const c of colliders){if(c.kind==='gable'||c.kind==='roof'||c.noStand||!insideXZ(c,x,z,.05))continue;if(c.top<=y+.5&&c.top>f)f=c.top;}const r=roofSurfaceAt(x,z);if(r!==null&&r<=y+.5&&r>f)f=r;return f;}
function lungeHoldCancel(){CHG.down=false;CHG.t=0;CHG.ready=false;}
function lungeReset(){
 CHG.down=false;CHG.t=0;CHG.fired=false;CHG.ready=false;player.lunge=null;player.block=null;BLOCK.cd=0;LUNGE.pw=0;LUNGE.glow=0;LUNGE.cd=0;LUNGE.samples.length=0;
 if(LUNGE.ring)LUNGE.ring.style.opacity='0';
}
function lungeSafe(fn,...a){try{return fn(...a);}catch(e){if(!lungeSafe.warned){lungeSafe.warned=true;console.error('[charged lunge]',e);}if(fn===blockMove)player.block=null;if(fn===lungeUpdate||fn===lungeMove){try{lungeReset();}catch(_){}}}}
// every frame, before the movement: charge timer, pose weight, hand-over from "charging" to "lunging"
function lungeUpdate(dt){
 upgHintUpdate();
 xpHud(dt);lvWallUpdate(dt);
 BLOCK.cd=Math.max(0,BLOCK.cd-dt);
 stamUpdate(dt);
 LUNGE.cd=Math.max(0,LUNGE.cd-dt);
 if(CHG.down){
  const A=erikaAnim,ok=running&&mouse.locked&&!playerDeath.active&&weapon==='sword'&&!player.slam&&!player.dash&&!player.kick&&!player.climbing&&!player.onWall&&!player.sliding&&!player.mantle&&!(grapplePull&&grapplePull.active)&&monsterRespawnTimer<=0&&!SUPER.aim&&!(A&&A.attackAction&&A.comboStep<1);
  if(!ok)lungeHoldCancel();
  else{CHG.t=Math.min(LUNGE.charge,CHG.t+dt);if(A&&A.attackAction&&CHG.t>LUNGE.delay)lungeCancelSlash();   // charging out of the 2nd/3rd slash: the slash gives way to the charge pose
   if(CHG.t>=LUNGE.charge&&!CHG.ready){   // charge complete: a light screen shake, then hold until the button is released
    CHG.ready=true;slamFx.shake=Math.max(slamFx.shake||0,.22);
    if(HFX.ready)hfxPut(HFX.flashes,_lg.fx.set(player.pos.x,player.pos.y+1.1,player.pos.z),.18,2.2,5,0xff5a3a);
    if(CHG.air&&!player.grounded&&!player.lunge){CHG.down=false;CHG.ready=false;CHG.fired=true;startLunge();}   // air charge: the lunge fires the instant the charge is full, no need to let go of the button
   }}
 }
 const L=player.lunge,charging=CHG.down&&CHG.t>LUNGE.delay;
 const want=L?(L.phase==='recover'?(L.t<.18?1:0):1):(charging?1:0);
 LUNGE.pw+=(want-LUNGE.pw)*(1-Math.exp(-(want>LUNGE.pw?16:9)*dt));if(LUNGE.pw<.004&&!want)LUNGE.pw=0;
 const gw=L?(L.phase==='recover'?Math.max(0,1-L.t/.3):1):(charging?THREE.MathUtils.clamp((CHG.t-LUNGE.delay)/(LUNGE.charge-LUNGE.delay),0,1)*(CHG.ready?1.1:.9):0);
 LUNGE.glow+=(gw-LUNGE.glow)*(1-Math.exp(-10*dt));if(LUNGE.glow<.004&&!gw)LUNGE.glow=0;
 lungeLeanStep(dt);
}
function lungeCancelSlash(){const A=erikaAnim;if(!A||!A.attackAction)return;for(const a of Object.values(A.attackActs))a.stop();for(const a of Object.values(A.attackUpper))a.stop();A.attackAction=null;A.atkFull=null;A.atkUpper=null;A.atkPrev=null;A.atkPrevUp=null;A.attackWeight=0;A.attackTarget=0;A.attackMove=0;A.comboStep=-1;A.comboUntil=0;A.slashQ=0;}
function startLunge(){
 try{lungeCancelSlash();}catch(e){}
 if(!stamSpend()){stamDeny();return;}
 const air=!player.grounded;let dx=-Math.sin(player.yaw),dz=-Math.cos(player.yaw),dy=0,travel=LUNGE.dist,best=null,bs=1e9;
 if(air){const cp=Math.cos(player.pitch);dx=-Math.sin(player.yaw)*cp;dz=-Math.cos(player.yaw)*cp;dy=Math.sin(player.pitch);}   // air lunge: straight along the crosshair, up / down / forward
 for(const m of monsters){   // light aim assist: a monster close to the crosshair line pulls the dash straight onto it
  if(!m.alive||m.entry||m.climb||m.roof)continue;
  const px=m.root.position.x-player.pos.x,pz=m.root.position.z-player.pos.z,d=Math.hypot(px,pz);
  if(air)continue;   // no aim assist in the air: the dash goes exactly where the crosshair points
  if(d<1||d>LUNGE.assistRange||Math.abs(m.root.position.y-player.pos.y)>3)continue;
  const dot=(px*dx+pz*dz)/d;if(dot<Math.cos(LUNGE.assist))continue;
  const sc=d*(1.25-dot);if(sc<bs){bs=sc;best=m;}
 }
 if(best){const px=best.root.position.x-player.pos.x,pz=best.root.position.z-player.pos.z,d=Math.hypot(px,pz);dx=px/d;dz=pz/d;travel=Math.min(LUNGE.dist,Math.max(5.5,d+1.8));}
 player.lunge={phase:'wind',t:0,u:0,dx,dz,dy,air,landed:false,travel,hit:new Set(),hits:0};
 LUNGE.cd=LUNGE.cool+LUNGE.wind+LUNGE.dur;
 player.sliding=false;player.jumpBuffer=0;
 playerHurtCooldown=Math.max(playerHurtCooldown,LUNGE.wind+LUNGE.dur+.25);   // a brief moment of invulnerability: the dash cuts straight through the pack
 try{slamSound('whoosh');}catch(e){}
 lungeFxInit();
 if(HFX.ready){const c=_lg.fx.set(player.pos.x,player.pos.y+1.1,player.pos.z);hfxPut(HFX.flashes,c,.2,2.6,6,0xff3a22);hfxPut(HFX.rings,_lg.fv.set(player.pos.x,player.pos.y+.12,player.pos.z),.34,.6,11,0xff2a1a);}
 slamFx.shake=Math.max(slamFx.shake||0,.2);
}
function lungeDashStart(L){
 DASH.fov=LUNGE.fov;DASH.from.copy(player.pos);DASH.dir.set(L.dx,0,L.dz);DASH.end.copy(player.pos);DASH.op=.8;
 slamFx.shake=Math.max(slamFx.shake||0,.4);
 try{slamSound('whoosh');}catch(e){}
 if(HFX.ready){
  const c=_lg.fx.set(player.pos.x,player.pos.y+.15,player.pos.z);
  hfxPut(HFX.flashes,_lg.fv.set(player.pos.x,player.pos.y+1.2,player.pos.z),.16,3.4,6,0xffe0c0);
  for(let i=0;i<26;i++){_dfx.v.set((Math.random()-.5)*5-L.dx*(6+Math.random()*10),Math.random()*4+.5,(Math.random()-.5)*5-L.dz*(6+Math.random()*10));dashSpark(c,_dfx.v,.28+Math.random()*.25,.14+Math.random()*.16,i%2?0xff3a22:0xffb070).grav=1;}
 }
}
function lungeHitMonster(m,L){
 const sc=m.cfg.scale;L.hits++;
 damageMonster(m,LUNGE.dmg,'sword');
 try{swordHitFx(m,2);}catch(e){}
 const A=m.anim;if(A){A.knockX+=L.dx*7/sc;A.knockZ+=L.dz*7/sc;}
 if(m.alive&&!m.boss){   // survivors are thrown up and fall sprawled, then get back up (same reaction as the leap strike)
  m.down={t:0,init:false,air:true,vy:Math.sqrt(2*JSTRIKE.grav*1.9),at:0,tt:0,fall:.25,lie:1.0};if(A)A.attackT=-1;
 }
 if(HFX.ready){
  const c=_lg.fx.set(m.root.position.x,m.root.position.y+1.3*sc,m.root.position.z);
  for(let i=0;i<18;i++){const th=Math.random()*6.283,sp=4+Math.random()*8;_dfx.v.set(Math.cos(th)*sp+L.dx*6,Math.random()*5+1,Math.sin(th)*sp+L.dz*6);dashSpark(c,_dfx.v,.3+Math.random()*.3,.14+Math.random()*.14,i%3?0xff3a22:0xffd090).grav=1;}
 }
 slamFx.shake=Math.max(slamFx.shake||0,.55);
}
function lungeHits(L,x0,z0,x1,z1){
 const ex=x1+L.dx*LUNGE.reach,ez=z1+L.dz*LUNGE.reach,ax=ex-x0,az=ez-z0,l2=ax*ax+az*az||1;
 for(const m of monsters){
  if(!m.alive||m.entry||m.climb||m.roof||L.hit.has(m))continue;
  const p=m.root.position,sc=m.cfg.scale;if(Math.abs(p.y-player.pos.y)>sc*2.4+1)continue;
  const t=Math.max(0,Math.min(1,((p.x-x0)*ax+(p.z-z0)*az)/l2));
  if(Math.hypot(x0+ax*t-p.x,z0+az*t-p.z)>LUNGE.width*.5+.5*sc)continue;
  L.hit.add(m);lungeHitMonster(m,L);
 }
}
// movement replaces resolveMovement while the lunge is playing (called from updateMovement)
function lungeHitsAir(L,x0,y0,z0,x1,y1,z1){   // 3D version for the air lunge: a capsule along the flight path against each monster's body centre
 const ex=x1+L.dx*LUNGE.reach,ey=y1+L.dy*LUNGE.reach,ez=z1+L.dz*LUNGE.reach,ax=ex-x0,ay=ey-y0,az=ez-z0,l2=ax*ax+ay*ay+az*az||1;
 for(const m of monsters){
  if(!m.alive||m.entry||m.climb||m.roof||L.hit.has(m))continue;
  const p=m.root.position,sc=m.cfg.scale,cy=p.y+.9*sc;
  const t=Math.max(0,Math.min(1,((p.x-x0)*ax+(cy-y0-1.1)*ay+(p.z-z0)*az)/l2));
  const qx=x0+ax*t-p.x,qy=y0+1.1+ay*t-cy,qz=z0+az*t-p.z;
  if(Math.hypot(qx,qy,qz)>LUNGE.width*.5+.6*sc+.4)continue;
  L.hit.add(m);lungeHitMonster(m,L);
 }
}
function lungeMove(dt){
 const L=player.lunge;if(!L)return;
 const air=L.air&&!L.landed;
 L.t+=dt;player.sliding=false;
 if(air){player.grounded=false;}else{player.grounded=true;player.airTime=0;player.vel.y=0;}
 if(L.phase==='wind'){
  const k=Math.exp(-16*dt);player.vel.x*=k;player.vel.z*=k;if(air)player.vel.y=0;
  if(L.t>=LUNGE.wind){L.phase='dash';L.t=0;L.u=0;lungeDashStart(L);}
  return;
 }
 if(L.phase==='dash'){
  const u0=L.u,u1=Math.min(1,L.t/LUNGE.dur),ease=u=>1-(1-u)*(1-u);L.u=u1;
  const step=(ease(u1)-ease(u0))*L.travel,x0=player.pos.x,y0=player.pos.y,z0=player.pos.z,n=Math.max(1,Math.ceil(step/.3));
  let blocked=false;
  for(let i=1;i<=n;i++){
   const nx=x0+L.dx*step*i/n,nz=z0+L.dz*step*i/n,ny=air?y0+L.dy*step*i/n:player.pos.y;
   if(Math.hypot(nx,nz)>WORLD.wallRadius-1.6){blocked=true;break;}
   for(const c of colliders){if(c.kind==='roof'||c.kind==='gable'||c.top<.5||c.top<=ny+.4)continue;if(c.bottom&&ny+1.65<c.bottom)continue;if(insideXZ(c,nx,nz,.43)){blocked=true;break;}}
   if(blocked)break;
   player.pos.x=nx;player.pos.z=nz;
   if(air){const fy=lungeFloorY(nx,nz,ny);if(ny<=fy){player.pos.y=fy;L.landed=true;blocked=true;break;}player.pos.y=ny;}
  }
  const sp=dt>0?step/dt:0;if(air&&!L.landed)player.vel.set(L.dx*sp,L.dy*sp,L.dz*sp);else player.vel.set(L.dx*sp,0,L.dz*sp);
  if(L.air)lungeHitsAir(L,x0,y0,z0,player.pos.x,player.pos.y,player.pos.z);else lungeHits(L,x0,z0,player.pos.x,player.pos.z);
  DASH.end.copy(player.pos);DASH.op=.8;
  if(HFX.ready){
   for(let i=0;i<7;i++){   // speed lines streaming past, embers kicked up from the floor
    const p=_lg.fx.set(player.pos.x+(Math.random()-.5)*2.2,player.pos.y+.2+Math.random()*1.8,player.pos.z+(Math.random()-.5)*2.2);
    _dfx.v.set(-L.dx*(8+Math.random()*10)+(Math.random()-.5)*1.5,-(L.dy||0)*(8+Math.random()*10)+(Math.random()-.5)*1.2,-L.dz*(8+Math.random()*10)+(Math.random()-.5)*1.5);
    dashSpark(p,_dfx.v,.2+Math.random()*.15,.12+Math.random()*.1,i%3===0?0xffe6d6:i%3===1?0xff3a22:0xc01010);
   }
   const g=_lg.fv.set(player.pos.x,player.pos.y+.1,player.pos.z);_dfx.v.set((Math.random()-.5)*3,1.5+Math.random()*2.5,(Math.random()-.5)*3);dashSpark(g,_dfx.v,.35,.2+Math.random()*.15,0xffa050).grav=1;
  }
  if(u1>=1||blocked){
   L.phase='recover';L.t=0;
   if(L.air&&!L.landed)player.vel.set(L.dx*3,Math.max(-2,Math.min(3,L.dy*3)),L.dz*3);else player.vel.set(L.dx*3,0,L.dz*3);
   slamFx.shake=Math.max(slamFx.shake||0,L.hits?.6:.3);try{if(!L.hits)slamSound('whoosh');}catch(e){}   // charged lunge: no ground-slam boom
   if(HFX.ready){
    const c=_lg.fx.set(player.pos.x,player.pos.y+.12,player.pos.z);hfxPut(HFX.rings,c,.4,.8,13,0xff3a22);
    const a=hfxPut(HFX.arcs,_lg.fv.set(player.pos.x+L.dx*1.2,player.pos.y+1.2+(L.dy||0)*1.2,player.pos.z+L.dz*1.2),.28,5.2,4,0xff5a3a);a.sx=1.6;a.s.material.rotation=1.57;   // crescent left hanging in the air by the cut
   }
  }
  return;
 }
 // recover: slide to a stop, then hand control back (in the air: gravity takes over again and the player falls / lands)
 const k=Math.exp(-9*dt);player.vel.x*=k;player.vel.z*=k;
 if(air){
  player.vel.y-=24*dt;player.pos.x+=player.vel.x*dt;player.pos.z+=player.vel.z*dt;player.pos.y+=player.vel.y*dt;
  const fy=lungeFloorY(player.pos.x,player.pos.z,player.pos.y+.3);if(player.pos.y<=fy){const fall=-player.vel.y;player.pos.y=fy;player.vel.y=0;L.landed=true;player.grounded=true;player.airTime=0;player.postFlight=false;if(fall>0){player.landImpact=fall;player.landEvent++;}}
 }
 if(L.t>=LUNGE.recover){if(L.air)player.postFlight=false;player.lunge=null;player.vel.x*=.3;player.vel.z*=.3;}
}
// rotate a bone about a WORLD axis (the mixer has just written its local rotation, so this is layered on top of the clip)
function lungeTurn(b,axis,ang){
 if(!b||Math.abs(ang)<1e-4)return;const S=_lg;
 b.updateWorldMatrix(true,false);b.getWorldQuaternion(S.q);b.parent.getWorldQuaternion(S.q2);
 S.q3.setFromAxisAngle(axis,ang);S.q.premultiply(S.q3);b.quaternion.copy(S.q2.invert().multiply(S.q));b.updateMatrixWorld(true);
}
// called at the end of the player animation update (same place as the ground-slam pose): torso twist / lean and both arms on the sword grip
function lungePoseIK(){
 const w=LUNGE.pw;if(!(w>.01)||!erikaPlayer||!erikaPlayer.bones||!playerMesh)return;
 const bn=erikaPlayer.bones,S=_lg,P=LUNGE.P;if(!bn.rightArm||!bn.leftArm||!bn.rightHand||!bn.leftHand)return;
 lungePose(P);
 playerMesh.updateMatrixWorld(true);playerMesh.getWorldQuaternion(S.pq);
 S.f.set(0,0,-1).applyQuaternion(S.pq);S.f.y=0;if(S.f.lengthSq()<1e-6)S.f.set(0,0,-1);S.f.normalize();
 S.r.set(1,0,0).applyQuaternion(S.pq);S.r.y=0;if(S.r.lengthSq()<1e-6)S.r.set(1,0,0);S.r.normalize();
 const sp=[bn.spine,bn.spine1,bn.spine2].filter(Boolean),chest=sp.length?sp[sp.length-1]:bn.hips;if(!chest)return;
 if(!LUNGE.la)for(const b of sp){lungeTurn(b,S.r,P.ln*w/sp.length);lungeTurn(b,S.u,P.tw*w/sp.length);}   // air: twist about the body's own axis (tiny), never a swirl around world-up
 playerMesh.updateMatrixWorld(true);chest.getWorldPosition(S.chest);
 S.G.copy(S.chest).addScaledVector(S.f,P.gf).addScaledVector(S.r,P.gr).addScaledVector(S.u,P.gu);
 S.B.set(0,0,0).addScaledVector(S.f,P.bf).addScaledVector(S.r,P.br).addScaledVector(S.u,P.bu).normalize();
 LUNGE.G.copy(S.G);LUNGE.B.copy(S.B);LUNGE.stamp=performance.now();
 S.T.copy(S.G).addScaledVector(S.B,.03);S.h.copy(S.r).multiplyScalar(.8).addScaledVector(S.u,-.5);slamArmIK(1,S.T,S.h,w);       // right hand just under the guard
 S.T.copy(S.G).addScaledVector(S.B,-.11);S.h.copy(S.r).multiplyScalar(-.8).addScaledVector(S.u,-.5);slamArmIK(-1,S.T,S.h,w);   // left hand near the pommel
}
// air lunge: the whole body tips smoothly along the strike line (pivot at the hips) instead of staying stiff upright
const _lbQ=new THREE.Quaternion(),_lbQ2=new THREE.Quaternion(),_lbV=new THREE.Vector3(),_lbAX=new THREE.Vector3(1,0,0),_lbAY=new THREE.Vector3(0,1,0),_lbAZ=new THREE.Vector3(0,0,1);
LUNGE.lean=0;LUNGE.leanDirty=false;LUNGE.la=false;
function lungeLeanStep(dt){
 const L=player.lunge;let tgt=0;
 if(false)tgt=THREE.MathUtils.clamp(.30-.55*(L.dy||0),-.30,.85);   // + = head forward
 const k=1-Math.exp(-(Math.abs(tgt)>Math.abs(LUNGE.lean)?12:6)*dt);
 LUNGE.lean+=(tgt-LUNGE.lean)*k;if(tgt===0&&Math.abs(LUNGE.lean)<.004)LUNGE.lean=0;
}
function lungeLeanApply(){
 if(!playerMesh)return;
 const A=erikaAnim,tl=(A&&A.tilt)||0,yy=player.yaw+(A&&A.ready&&thirdPerson?A.heading+(A.aimYawOff||0):0);
 if(!thirdPerson||Math.abs(LUNGE.lean)<.003){if(LUNGE.leanDirty){playerMesh.rotation.set(0,yy,tl);LUNGE.leanDirty=false;}return;}
 _lbQ.setFromAxisAngle(_lbAY,yy);_lbQ2.setFromAxisAngle(_lbAX,-LUNGE.lean);_lbQ.multiply(_lbQ2);_lbQ2.setFromAxisAngle(_lbAZ,tl);_lbQ.multiply(_lbQ2);
 playerMesh.quaternion.copy(_lbQ);_lbV.set(0,.95,0).applyQuaternion(_lbQ);
 playerMesh.position.set(player.pos.x-_lbV.x,player.pos.y-superCrouchDrop()+.95-_lbV.y,player.pos.z-_lbV.z);LUNGE.leanDirty=true;
}
// the sword follows the real palms while the pose is active (first and third person)
function lungeSwordOverride(dt){
 const w=LUNGE.pw,g=sword.group;if(!(w>.01)||!g||!g.visible||performance.now()-LUNGE.stamp>90||!erikaPlayer||!erikaPlayer.bones||!playerMesh)return;
 const bn=erikaPlayer.bones,S=_lg;if(!bn.rightHand||!bn.leftHand)return;
 palmWorld(bn.rightHand,'mixamorigRightHandMiddle1',S.v1);palmWorld(bn.leftHand,'mixamorigLeftHandMiddle1',S.v2);
 const B=S.B.copy(LUNGE.B);
 S.T.copy(S.v1).add(S.v2).multiplyScalar(.5).addScaledVector(B,.04);
 S.Z.copy(S.u).addScaledVector(B,-S.u.dot(B));if(S.Z.lengthSq()<1e-4)S.Z.copy(S.r).addScaledVector(B,-S.r.dot(B));S.Z.normalize();   // flat of the blade faces up / down: the edge leads the cut
 S.X.crossVectors(B,S.Z).normalize();S.m.makeBasis(S.X,B,S.Z);S.q.setFromRotationMatrix(S.m);
 const k=THREE.MathUtils.smoothstep(w,0,1);
 g.position.lerp(S.T,k);g.quaternion.slerp(S.q,k);
}
// ---- visual effects ----------------------------------------------------------------------------------------------------------------------
function lungeFxInit(){
 if(LUNGE.init||!scene||!sword.group)return;LUNGE.init=true;
 const g=sword.group;
 // glowing aura around the blade + hot spots, driven by LUNGE.glow
 LUNGE.auraMat=new THREE.MeshBasicMaterial({color:0xff2a14,transparent:true,opacity:0,depthWrite:false,blending:THREE.AdditiveBlending,fog:false});
 const aura=new THREE.Mesh(new THREE.BoxGeometry(.11,1.3,.11),LUNGE.auraMat);aura.position.y=.146+.65;aura.frustumCulled=false;aura.renderOrder=18;g.add(aura);LUNGE.aura=aura;
 const tex=(typeof hfxTexSafe==='function')?hfxTexSafe():null;
 for(const y of [.25,.7,1.15,1.45]){
  const sp=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,color:0xff3a22,transparent:true,opacity:0,depthWrite:false,blending:THREE.AdditiveBlending,fog:false}));
  sp.position.set(0,y,0);sp.scale.set(.5,.5,1);sp.frustumCulled=false;sp.renderOrder=18;g.add(sp);LUNGE.glows.push(sp);
 }
 g.traverse(o=>{if(!LUNGE.swordMat&&o.isMesh&&o.material&&o.material.isMeshStandardMaterial&&o.material.emissive.r>.02&&o.material.emissive.g<.02){LUNGE.swordMat=o.material;LUNGE.swordMatI=o.material.emissiveIntensity;}});
 // blade trail: a ribbon between the tip and the base of the blade
 const N=44,geo=new THREE.BufferGeometry();
 geo.setAttribute('position',new THREE.BufferAttribute(new Float32Array(N*6),3));geo.setAttribute('color',new THREE.BufferAttribute(new Float32Array(N*6),3));
 const idx=[];for(let i=0;i<N-1;i++){const a=i*2;idx.push(a,a+1,a+2,a+1,a+3,a+2);}geo.setIndex(idx);geo.setDrawRange(0,0);
 const mesh=new THREE.Mesh(geo,new THREE.MeshBasicMaterial({vertexColors:true,transparent:true,blending:THREE.AdditiveBlending,depthWrite:false,side:THREE.DoubleSide,fog:false}));
 mesh.frustumCulled=false;mesh.renderOrder=19;mesh.visible=false;scene.add(mesh);LUNGE.trail=mesh;LUNGE.trailN=N;
}
function lungeRingEl(){
 if(LUNGE.ring)return LUNGE.ring;
 const el=document.createElement('div');
 el.style.cssText='position:fixed;left:50%;top:50%;width:104px;height:104px;margin:-52px 0 0 -52px;border-radius:50%;pointer-events:none;z-index:3;opacity:0;transition:opacity .12s;-webkit-mask:radial-gradient(circle,transparent 43px,#000 44px,#000 49px,transparent 50px);mask:radial-gradient(circle,transparent 43px,#000 44px,#000 49px,transparent 50px);';
 const host=document.getElementById('screen')||document.body;host.appendChild(el);LUNGE.ring=el;return el;
}
function lungeFxUpdate(dt){
 stamHud();
 if(!LUNGE.init&&(player.lunge||CHG.down))lungeFxInit();
 // charge ring around the crosshair
 {const L=player.lunge,showing=CHG.down&&CHG.t>LUNGE.delay&&!L;
  if(showing||LUNGE.ringOn){const el=lungeRingEl(),p=THREE.MathUtils.clamp((CHG.t-LUNGE.delay)/(LUNGE.charge-LUNGE.delay),0,1);
   el.style.opacity=showing?'1':'0';
   if(showing){const hot=p>.9;el.style.background='conic-gradient(from 0deg,'+(hot?'rgba(255,235,200,.98)':'rgba(255,70,40,.95)')+' '+(p*360).toFixed(1)+'deg,rgba(255,255,255,.08) 0)';el.style.filter='drop-shadow(0 0 '+(4+p*10).toFixed(1)+'px rgba(255,50,30,.9))';}
   LUNGE.ringOn=showing;}}
 if(!LUNGE.init)return;
 const g=sword.group,gl=LUNGE.glow;
 if(g&&LUNGE.auraMat){
  const pulse=1+.18*Math.sin(performance.now()*.03);
  LUNGE.auraMat.opacity=Math.min(.75,gl*.8)*pulse;LUNGE.aura.visible=gl>.01;
  for(const sp of LUNGE.glows){sp.material.opacity=Math.min(1,gl)*.9;sp.scale.setScalar(.35+gl*.7*pulse);sp.visible=gl>.01;}
  if(LUNGE.swordMat)LUNGE.swordMat.emissiveIntensity=LUNGE.swordMatI+gl*3.2;
 }
 // energy gathering into the blade while charging
 if(HFX.ready&&CHG.down&&CHG.t>LUNGE.delay&&!player.lunge&&g&&g.visible&&dt>0){
  const p=THREE.MathUtils.clamp((CHG.t-LUNGE.delay)/(LUNGE.charge-LUNGE.delay),0,1),n=Math.random()<.4+p*.9?1+(p>.6?1:0):0;
  g.updateMatrixWorld(true);
  for(let i=0;i<n;i++){
   const tip=g.localToWorld(_lg.tip.set(0,.3+Math.random()*1.1,0)),a=Math.random()*6.283,rr=.7+Math.random()*.8;
   _lg.fx.set(tip.x+Math.cos(a)*rr,tip.y+(Math.random()-.5)*rr,tip.z+Math.sin(a)*rr);
   _dfx.v.copy(tip).sub(_lg.fx).multiplyScalar(3.2);dashSpark(_lg.fx,_dfx.v,.3,.1+Math.random()*.1,Math.random()<.4?0xffd0b0:0xff2a14);
  }
  if(p>.7)slamFx.shake=Math.max(slamFx.shake||0,(p-.7)*.07);
 }
 // blade trail
 const T=LUNGE.trail;if(!T)return;
 const L=player.lunge,on=!!L&&(L.phase==='dash'||(L.phase==='recover'&&L.t<.1))&&g&&g.visible,S=LUNGE.samples,now=performance.now()*.001;
 if(on&&dt>0){g.updateMatrixWorld(true);S.push({t:now,tip:g.localToWorld(new THREE.Vector3(0,1.42,0)),base:g.localToWorld(new THREE.Vector3(0,.3,0))});if(S.length>LUNGE.trailN)S.shift();}
 while(S.length&&now-S[0].t>.3)S.shift();
 if(S.length<2){T.visible=false;return;}
 T.visible=true;const pa=T.geometry.attributes.position,ca=T.geometry.attributes.color;
 for(let i=0;i<S.length;i++){
  const s=S[i],a=Math.pow(Math.max(0,1-(now-s.t)/.3),1.4);
  pa.setXYZ(i*2,s.tip.x,s.tip.y,s.tip.z);pa.setXYZ(i*2+1,s.base.x,s.base.y,s.base.z);
  ca.setXYZ(i*2,1*a,.62*a,.4*a);ca.setXYZ(i*2+1,.75*a,.04*a,.03*a);
 }
 pa.needsUpdate=true;ca.needsUpdate=true;T.geometry.setDrawRange(0,(S.length-1)*6);
}
function triggerSwordSlash(){
 if(player.dash||player.lunge||player.block)return;
 if(!running||weapon!=='sword'||player.slam||!player.grounded||player.sliding||player.climbing||player.onWall||player.postFlight||(grapplePull&&grapplePull.active))return;const A=erikaAnim;if(!A.ready||!A.attackActs)return;
 if(A.attackAction){if(A.comboStep>=0&&A.comboStep<=2){if(swordSlashU(A)>=SWORD_FAST.cancelAt[A.comboStep])swordChain(A);else A.slashQ=performance.now()+SWORD_FAST.buffer*1000;}return;}
 const now=performance.now();if(A.comboUntil&&now>A.comboUntil){A.comboStep=-1;A.comboUntil=0;}
 const step=A.comboUntil>0&&A.comboStep>=0&&A.comboStep<2?A.comboStep+1:0;
 const names=['SwordSlash','SecondSwordSlash','ThirdSwordSlash'],name=names[step];if(!A.attackActs[name])return;
 {const dm=pickDashTarget();if(dm){A.comboUntil=0;startSwordDash(dm,step);return;}}   // monster under the crosshair within 4 m: dash first
 A.comboStep=step;A.comboUntil=0;startErikaSwordAttack(name);
}
function startBowDraw(){if(!running||!bow.group)return;if(weapon!=='bow'){showToast('PRESS '+keyLabel('bow')+' FOR THE BOW');return;}if(bow.drawing){bow.pendingRelease=false;return;}if(AMMO.cur<=0){showToast('OUT OF ARROWS - CLEAR THE WAVE TO REFILL');return;}bow.drawing=true;bow.draw=0;sound('draw');}   // may start during the cooldown
function cancelBowDraw(){bow.drawing=false;bow.draw=0;bow.pendingRelease=false;}
function startAim(){if(!running||!bow.group)return;if(weapon!=='bow'){showToast('PRESS '+keyLabel('bow')+' FOR THE BOW');return;}bow.aiming=true;}
function stopAim(){bow.aiming=false;cancelBowDraw();}
function releaseBow(){
 if(!bow.drawing)return;
 if(bow.draw<.999){cancelBowDraw();return;}
 if(AMMO.cur<=0){cancelBowDraw();return;}   // released before the string was pulled all the way back: no arrow
 if(bow.cool>0){bow.pendingRelease=true;return;}   // released during the cooldown: the arrow flies the moment it ends
 bow.pendingRelease=false;const p=1;bow.drawing=false;
 if(!running||!bow.group){bow.draw=0;return;}
 bow.group.updateMatrixWorld(true);
 const origin=bow.group.localToWorld(v3(BOW_ARROW_RIGHT_OFFSET,0,-.2));
 const cdir=cameraDir();
 const target=camera.position.clone().addScaledVector(cdir,300);
 const hit=raycastTarget(camera.position.clone(),cdir,500);if(hit)target.copy(hit.point);
 const dir=target.clone().sub(origin);
 if(dir.lengthSq()<9||dir.dot(cdir)<.2)dir.copy(cdir);
 dir.normalize();
 // Keep the arrow ahead of the player when flying fast along the aim direction.
 const along=Math.max(0,player.vel.dot(dir));
 const speed=THREE.MathUtils.lerp(BOW.minSpeed,BOW.maxSpeed,p)+along*.9;
 const mesh=makeArrowMesh();mesh.scale.setScalar(1.5);mesh.position.copy(origin);mesh.userData.trail.visible=false;scene.add(mesh);
 const trail=createArrowPathTrail(origin);arrowReleaseFx(origin,dir,p);bow.arrows.push({mesh,pos:origin.clone(),vel:dir.clone().multiplyScalar(speed),state:'fly',life:0,trail,power:p});
 while(bow.arrows.length>BOW.maxStuck)disposeArrow(bow.arrows.shift());
 bow.draw=0;bow.cool=BOW.cooldown;sound('bow');AMMO.cur=Math.max(0,AMMO.cur-1);
}
const ARROW_TRAIL_POINT_LIMIT=384;
function createArrowPathTrail(start){
 const geometry=new THREE.BufferGeometry(),positions=new Float32Array(ARROW_TRAIL_POINT_LIMIT*3);
 positions[0]=positions[3]=start.x;positions[1]=positions[4]=start.y;positions[2]=positions[5]=start.z;
 const attribute=new THREE.BufferAttribute(positions,3);attribute.setUsage(THREE.DynamicDrawUsage);geometry.setAttribute('position',attribute);geometry.setDrawRange(0,2);
 const material=bow.mats.trail.clone();material.color.setHex(0xd01414);material.opacity=.7;material.depthWrite=false;
 const line=new THREE.Line(geometry,material);line.frustumCulled=false;scene.add(line);
 return{line,attribute,positions,points:[start.clone(),start.clone()],opacity:.7};
}
function updateArrowPathTrail(a){
 const t=a.trail;if(!t)return;const points=t.points,last=points[points.length-1];
 if(last.distanceToSquared(a.pos)>.09){points.push(a.pos.clone());if(points.length>ARROW_TRAIL_POINT_LIMIT)points.shift();}else last.copy(a.pos);
 for(let i=0;i<points.length;i++){const p=points[i],j=i*3;t.positions[j]=p.x;t.positions[j+1]=p.y;t.positions[j+2]=p.z;}
 t.attribute.needsUpdate=true;t.line.geometry.setDrawRange(0,points.length);
}
function disposeArrow(a){
 if(a.mesh)scene.remove(a.mesh);
 if(a.trail){scene.remove(a.trail.line);a.trail.line.geometry.dispose();a.trail.line.material.dispose();a.trail=null;}
}
function updateBow(dt){
 // weapons are put away while climbing and come back shortly after the climb ends
 if(player.climbing){climbHideT=.28;if(bow.aiming||bow.drawing)stopAim();}else climbHideT=Math.max(0,climbHideT-(dt>0?dt:0));
 weaponsHidden=climbHideT>0;
 updateErikaFPMask();
 updateSword(dt);
 if(!bow.group||!playerMesh||!camera)return;
 if(dt>0){
  if(bow.cool>0)bow.cool=Math.max(0,bow.cool-dt);
  if(bow.pendingRelease&&bow.cool<=0){releaseBow();stopAim();}
  if(bow.drawing){bow.draw=Math.min(1,bow.draw+dt/BOW.drawTime);bow.hold=.4;}
  else bow.hold=Math.max(0,bow.hold-dt);
  const want=(weapon==='bow'&&(bow.aiming||bow.drawing||bow.hold>0))?1:0;
  bow.carry+=((weapon==='bow'?1:0)-bow.carry)*(1-Math.exp(-12*dt));
  bow.aimW+=(((bow.aiming||bow.drawing)?1:0)-bow.aimW)*(1-Math.exp(-11*dt));if(bow.aimW<.002)bow.aimW=0;
  const _cz=(CHG.down&&!player.lunge&&CHG.t>LUNGE.delay)?THREE.MathUtils.clamp((CHG.t-LUNGE.delay)/(LUNGE.charge-LUNGE.delay),0,1):0;CHG.zoom=(CHG.zoom||0)+(_cz*_cz*(3-2*_cz)-(CHG.zoom||0))*(1-Math.exp(-9*Math.min(dt||.016,.05)));const fovT=GFX.fov-26*bow.aimW+DASH.fov-LUNGE.zoomFov*CHG.zoom;if(Math.abs(camera.fov-fovT)>.02){camera.fov=fovT;camera.updateProjectionMatrix();}
  bow.equip+=(want-bow.equip)*(1-Math.exp(-14*dt));
  if(!want&&bow.equip<.003)bow.equip=0;
 }
 playerMesh.updateMatrixWorld(true);
 const pq=playerMesh.getWorldQuaternion(new THREE.Quaternion());
 const backBone=erikaPlayer&&erikaPlayer.bones&&(erikaPlayer.bones.spine2||erikaPlayer.bones.spine||erikaPlayer.bones.hips);
 const base=new THREE.Vector3(),bodyQ=backBone?backBone.getWorldQuaternion(new THREE.Quaternion()):pq;if(backBone)backBone.getWorldPosition(base);else base.set(player.pos.x,player.pos.y+1,player.pos.z);
 // The bow stays behind the upper torso and follows its animation.
 const stowOffset=erikaPlayer&&erikaPlayer.backOffset?erikaPlayer.backOffset.clone().applyQuaternion(bodyQ):new THREE.Vector3(.04,.5,.5).applyQuaternion(pq);
 const stowPos=base.clone().add(stowOffset);
 const stowQ=backBone&&erikaPlayer&&erikaPlayer.backRotation?bodyQ.clone().multiply(erikaPlayer.backRotation):pq.clone().multiply(new THREE.Quaternion().setFromEuler(new THREE.Euler(0,0,-.55)));
 // Aimed: first person = view model, third person = left hand.
 const cdir=cameraDir();
 let aimPos,aimQ,scale;
 if(!thirdPerson){
  aimPos=new THREE.Vector3(-.27+.1*bow.aimW,-.2+.05*bow.aimW,-.7).applyQuaternion(camera.quaternion).add(camera.position);
  aimQ=camera.quaternion.clone();scale=.78;
 }else{
  const lh=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.leftHand;
  aimPos=new THREE.Vector3();if(lh)lh.getWorldPosition(aimPos);else aimPos.copy(base).addScaledVector(cdir,.5);
  aimPos.addScaledVector(cdir,.08);
  _bowObj.position.copy(aimPos);_bowObj.lookAt(aimPos.clone().sub(cdir));aimQ=_bowObj.quaternion.clone();scale=.9;
 }
 const e=bow.equip*bow.equip*(3-2*bow.equip),ce=bow.carry*bow.carry*(3-2*bow.carry);
 // Carried (bow selected, not aiming): held in the right hand like the sword.
 const carryPos=new THREE.Vector3(),lhb=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.leftHand;
 if(lhb)palmWorld(lhb,'mixamorigLeftHandMiddle1',carryPos);else carryPos.copy(base);
 const carryRef=thirdPerson?pq:camera.quaternion,carryWob=(lhb&&bow.carry>.02)?handWobble(bowSlot,lhb,carryRef,dt,thirdPerson?'tp':'fp'):null;
 let carryQ,carryScale;
 if(!thirdPerson){carryQ=camera.quaternion.clone();if(carryWob)carryQ.multiply(carryWob);carryQ.multiply(new THREE.Quaternion().setFromEuler(new THREE.Euler(-.25,.3,.1)));carryScale=.7;}
 else{carryQ=pq.clone();if(carryWob)carryQ.multiply(carryWob);carryQ.multiply(new THREE.Quaternion().setFromEuler(new THREE.Euler(-.2,0,.08)));carryScale=.85;}
 const restPos=new THREE.Vector3().lerpVectors(stowPos,carryPos,ce),restQ=stowQ.clone().slerp(carryQ,ce),restScale=THREE.MathUtils.lerp(.9,carryScale,ce);
 bow.group.position.lerpVectors(restPos,aimPos,e);
 bow.group.quaternion.slerpQuaternions(restQ,aimQ,e);
 bow.group.scale.setScalar(THREE.MathUtils.lerp(restScale,scale,e));
 bow.group.visible=!weaponsHidden&&(thirdPerson||bow.equip>.02||bow.carry>.02);
 // string + nocked arrow
 const nockZ=.06+.5*Math.max(bow.draw,.18*bow.aimW);
 const pos=bow.string.geometry.attributes.position;pos.setXYZ(1,BOW_ARROW_RIGHT_OFFSET,0,nockZ);pos.needsUpdate=true;
 bow.nocked.visible=bow.drawing&&bow.equip>.5&&!player.block;bow.nocked.position.set(BOW_ARROW_RIGHT_OFFSET,0,nockZ-.8);
 // third person: the right hand grips the bowstring and follows it while drawing
 if(thirdPerson&&!weaponsHidden&&weapon==='bow')bowStringHandIK(nockZ,e*bow.aimW);
 // HUD
 const key=(bow.drawing?'d'+Math.round(bow.draw*100):bow.cool>0?'c':'r')+(bow.aiming?'a':'');
 if(key!==bow.uiKey){
  bow.uiKey=key;const box=$('bowBox'),st=$('bowState'),fill=$('bowFill'),ch=$('crosshair');
  if(box)box.classList.toggle('active',bow.drawing||bow.aiming||bow.cool>0);
  if(st)st.textContent=bow.drawing?(bow.draw>=.999?'FULL - RELEASE':'DRAW '+Math.round(bow.draw*100)+'%'):bow.cool>0?'NOCKING':bow.aiming?'AIMING':'READY';
  if(fill)fill.style.width=(bow.drawing?bow.draw*100:0)+'%';
  if(ch)ch.classList.toggle('aiming',bow.drawing||bow.aiming);
  {   // draw bar under the crosshair: fills while the string is pulled, must be completely full to shoot
   let bar=document.getElementById('bowDrawBar');
   if(!bar){const stl=document.createElement('style');stl.textContent='#bowDrawBar{position:absolute;left:50%;top:calc(50% + 24px);width:72px;height:4px;transform:translateX(-50%);border-radius:4px;background:rgba(0,0,0,.55);border:1px solid rgba(246,237,219,.6);box-shadow:0 0 6px #000;overflow:hidden;opacity:0;transition:opacity .12s}#bowDrawBar i{display:block;height:100%;width:0;background:linear-gradient(90deg,#c98a2e,#f3c870)}#bowDrawBar.full{border-color:#7dffa0;box-shadow:0 0 10px rgba(125,255,160,.9)}#bowDrawBar.full i{background:#7dffa0}';document.head.appendChild(stl);
    bar=document.createElement('div');bar.id='bowDrawBar';bar.innerHTML='<i></i>';(document.getElementById('screen')||document.body).appendChild(bar);}
   bar.style.opacity=(bow.drawing||bow.aiming)?'1':'0';bar.firstChild.style.width=(bow.drawing?bow.draw*100:0)+'%';bar.classList.toggle('full',bow.drawing&&bow.draw>=.999);
  }
 }
}

// ---- Right hand grips the bowstring (third person): two-bone IK on RightArm / RightForeArm, applied after the aim animation.
const _ik={A:new THREE.Vector3(),B:new THREE.Vector3(),C:new THREE.Vector3(),T:new THREE.Vector3(),W:new THREE.Vector3(),d:new THREE.Vector3(),
 p:new THREE.Vector3(),dir:new THREE.Vector3(),Bn:new THREE.Vector3(),f:new THREE.Vector3(),r:new THREE.Vector3(),h:new THREE.Vector3(),
 v1:new THREE.Vector3(),v2:new THREE.Vector3(),q:new THREE.Quaternion(),q2:new THREE.Quaternion(),wq:new THREE.Quaternion(),pq:new THREE.Quaternion()};
function _ikTurnBone(bone,from,to,w){
 const I=_ik;I.q.setFromUnitVectors(from,to);I.q2.identity().slerp(I.q,w);
 bone.getWorldQuaternion(I.wq);bone.parent.getWorldQuaternion(I.pq);
 I.wq.premultiply(I.q2);bone.quaternion.copy(I.pq.invert().multiply(I.wq));bone.updateMatrixWorld(true);
}
function bowStringHandIK(nockZ,w){
 const bn=erikaPlayer&&erikaPlayer.bones;if(!bn||!bn.rightArm||!bn.rightForeArm||!bn.rightHand||!(w>.01))return;
 const up=bn.rightArm,fo=bn.rightForeArm,ha=bn.rightHand,I=_ik;
 bow.group.updateMatrixWorld(true);playerMesh.updateMatrixWorld(true);
 I.T.set(BOW_ARROW_RIGHT_OFFSET,0,nockZ);bow.group.localToWorld(I.T);
 // During flight, bend the drawing arm forward and outward so the wrist stays in front of the torso.
 const cd=cameraDir();I.f.set(cd.x,0,cd.z);if(I.f.lengthSq()<1e-6)I.f.set(0,0,-1);I.f.normalize();
 const aerialBowAim=thirdPerson&&!player.grounded&&(player.state==='GRAPPLING'||player.state==='HOOK LAUNCH'||player.postFlight);I.r.set(-I.f.z,0,I.f.x);I.h.set(0,aerialBowAim?-.06:.15,0).addScaledVector(I.f,aerialBowAim?1.15:.8).addScaledVector(I.r,aerialBowAim?.95:.65);
 for(let pass=0;pass<2;pass++){
  up.getWorldPosition(I.A);fo.getWorldPosition(I.B);ha.getWorldPosition(I.C);
  const L1=I.A.distanceTo(I.B),L2=I.B.distanceTo(I.C);if(L1<1e-4||L2<1e-4)return;
  // wrist target = string point minus the wrist→finger-grip offset
  palmWorld(ha,'mixamorigRightHandMiddle1',I.v1);I.d.copy(I.v1).sub(I.C);
  I.W.copy(I.T).addScaledVector(I.d,-.85);
  I.dir.copy(I.W).sub(I.A);let dist=I.dir.length();if(dist<1e-4)return;I.dir.divideScalar(dist);
  dist=THREE.MathUtils.clamp(dist,Math.abs(L1-L2)+.02,(L1+L2)*.998);
  I.p.copy(I.h).addScaledVector(I.dir,-I.h.dot(I.dir));
  if(I.p.lengthSq()<1e-6)I.p.set(0,-1,0).addScaledVector(I.dir,I.dir.y);
  I.p.normalize();
  const cosA=THREE.MathUtils.clamp((L1*L1+dist*dist-L2*L2)/(2*L1*dist),-1,1),sinA=Math.sqrt(1-cosA*cosA);
  I.Bn.copy(I.A).addScaledVector(I.dir,L1*cosA).addScaledVector(I.p,L1*sinA);
  I.v1.copy(I.B).sub(I.A).normalize();I.v2.copy(I.Bn).sub(I.A).normalize();
  _ikTurnBone(up,I.v1,I.v2,w);
  fo.getWorldPosition(I.B);ha.getWorldPosition(I.C);
  I.v1.copy(I.C).sub(I.B).normalize();I.v2.copy(I.W).sub(I.B).normalize();
  _ikTurnBone(fo,I.v1,I.v2,w);
 }
}
// Keep the bow hand in front of the chest while aiming during flight; the bow and string hand follow it.
function bowAerialLeftHandIK(w){
 const bn=erikaPlayer&&erikaPlayer.bones;if(!bn||!bn.leftArm||!bn.leftForeArm||!bn.leftHand||!(w>.01)||!playerMesh)return;
 const up=bn.leftArm,fo=bn.leftForeArm,ha=bn.leftHand,I=_ik,chest=bn.spine2||bn.spine1||bn.spine||bn.hips;if(!chest)return;
 playerMesh.updateMatrixWorld(true);chest.getWorldPosition(I.T);playerMesh.getWorldQuaternion(I.pq);
 I.f.set(0,0,-1).applyQuaternion(I.pq);I.f.y=0;if(I.f.lengthSq()<1e-6)I.f.set(0,0,-1);I.f.normalize();
 I.r.set(1,0,0).applyQuaternion(I.pq);I.r.y=0;if(I.r.lengthSq()<1e-6)I.r.set(1,0,0);I.r.normalize();
 // Place the bow grip forward and slightly left of the chest, rather than following the raised flight pose.
 I.T.addScaledVector(I.f,.42).addScaledVector(I.r,-.36);I.T.y+=.10;
 up.getWorldPosition(I.A);fo.getWorldPosition(I.B);ha.getWorldPosition(I.C);palmWorld(ha,'mixamorigLeftHandMiddle1',I.v1);I.d.copy(I.v1).sub(I.C);I.W.copy(I.T).addScaledVector(I.d,-.85);
 I.h.copy(I.f).multiplyScalar(.7).addScaledVector(I.r,-.55);I.h.y=-.12;
 for(let pass=0;pass<2;pass++){
  up.getWorldPosition(I.A);fo.getWorldPosition(I.B);ha.getWorldPosition(I.C);
  const L1=I.A.distanceTo(I.B),L2=I.B.distanceTo(I.C);if(L1<1e-4||L2<1e-4)return;
  I.dir.copy(I.W).sub(I.A);let dist=I.dir.length();if(dist<1e-4)return;I.dir.divideScalar(dist);
  dist=THREE.MathUtils.clamp(dist,Math.abs(L1-L2)+.02,(L1+L2)*.998);
  I.p.copy(I.h).addScaledVector(I.dir,-I.h.dot(I.dir));if(I.p.lengthSq()<1e-6)I.p.set(0,-1,0).addScaledVector(I.dir,I.dir.y);I.p.normalize();
  const cosA=THREE.MathUtils.clamp((L1*L1+dist*dist-L2*L2)/(2*L1*dist),-1,1),sinA=Math.sqrt(1-cosA*cosA);
  I.Bn.copy(I.A).addScaledVector(I.dir,L1*cosA).addScaledVector(I.p,L1*sinA);
  I.v1.copy(I.B).sub(I.A).normalize();I.v2.copy(I.Bn).sub(I.A).normalize();_ikTurnBone(up,I.v1,I.v2,w);
  fo.getWorldPosition(I.B);ha.getWorldPosition(I.C);I.v1.copy(I.C).sub(I.B).normalize();I.v2.copy(I.W).sub(I.B).normalize();_ikTurnBone(fo,I.v1,I.v2,w);
 }
}
const _arrowFwd=new THREE.Vector3(0,0,-1),_arrowDir=new THREE.Vector3();
let monsterMaterials=null,monsterOrganicGeometry=null,monsterSpitGeometry=null,monsterSpitMaterial=null,monsterAnimations=null,monsterAnimationModule=null;
let monsterHealthFill=null,monsterHealthText=null,monsterThreatText=null,monsterHurtFlash=null;
let playerHealth=100,playerHurtCooldown=0,monsterRespawnTimer=0,monsterKills=0,monsterHudTimer=0;
const playerDeath={active:false,started:false,shown:false,t:0,wasThird:false};
function makeMonsterSkinTexture(seed,base){
 const canvas=document.createElement('canvas');canvas.width=256;canvas.height=256;const ctx=canvas.getContext('2d'),img=ctx.createImageData(256,256);let state=seed>>>0;
 const rand=()=>{state=(state*1664525+1013904223)>>>0;return state/4294967296;};
 for(let y=0;y<256;y++)for(let x=0;x<256;x++){const i=(y*256+x)*4;const wave=Math.sin(x*.067+seed)*7+Math.sin(y*.081-seed*.6)*6+Math.sin((x+y)*.035+seed)*4;const pore=rand()<.025?-20:0,n=wave+(rand()-.5)*30+pore;img.data[i]=THREE.MathUtils.clamp(base[0]+n,0,255);img.data[i+1]=THREE.MathUtils.clamp(base[1]+n,0,255);img.data[i+2]=THREE.MathUtils.clamp(base[2]+n,0,255);img.data[i+3]=255;}
 ctx.putImageData(img,0,0);ctx.lineCap='round';for(let i=0;i<18;i++){const x=rand()*256,y=rand()*256;ctx.strokeStyle=i%3?'rgba(37,18,17,.18)':'rgba(196,150,127,.13)';ctx.lineWidth=.7+rand()*1.5;ctx.beginPath();ctx.moveTo(x,y);ctx.bezierCurveTo(x+(rand()-.5)*18,y+rand()*12,x+(rand()-.5)*28,y+rand()*22,x+(rand()-.5)*34,y+rand()*34);ctx.stroke();}
 const tex=new THREE.CanvasTexture(canvas);tex.colorSpace=THREE.SRGBColorSpace;tex.wrapS=tex.wrapT=THREE.RepeatWrapping;tex.repeat.set(1.5,1.5);tex.needsUpdate=true;return tex;
}
function setupMonsterMaterials(){
 if(monsterMaterials)return;
 monsterOrganicGeometry=new THREE.SphereGeometry(1,24,18);const p=monsterOrganicGeometry.attributes.position;
 for(let i=0;i<p.count;i++){const x=p.getX(i),y=p.getY(i),z=p.getZ(i),n=1+.014*Math.sin(x*12.4+y*8.1+z*5.3)*Math.sin(z*10.2-y*6.7);p.setXYZ(i,x*n,y*n,z*n);}monsterOrganicGeometry.computeVertexNormals();
 const skin=(seed,rgb)=>{const tex=makeMonsterSkinTexture(seed,rgb);return new THREE.MeshStandardMaterial({map:tex,bumpMap:tex,bumpScale:.045,roughness:.86,metalness:0});};
 monsterMaterials={skin:{brute:skin(17,[112,91,84]),stalker:skin(43,[75,73,69]),spitter:skin(81,[95,101,72])},dark:new THREE.MeshStandardMaterial({color:0x352d2c,roughness:.94}),mouth:new THREE.MeshStandardMaterial({color:0x17090b,roughness:.98}),socket:new THREE.MeshStandardMaterial({color:0x241b1b,roughness:.95}),tooth:new THREE.MeshStandardMaterial({color:0xc7b99e,roughness:.55}),claw:new THREE.MeshStandardMaterial({color:0x282321,roughness:.62,metalness:.12}),bruteArmor:new THREE.MeshStandardMaterial({color:0x49413d,roughness:.9}),stalkerPlate:new THREE.MeshStandardMaterial({color:0x373d3b,roughness:.9}),spitterSack:new THREE.MeshStandardMaterial({color:0x697244,roughness:.67,bumpScale:.025}),scar:new THREE.MeshStandardMaterial({color:0x492c2c,roughness:.95}),eyes:{brute:new THREE.MeshStandardMaterial({color:0x7e2117,emissive:0x68180f,emissiveIntensity:.65,roughness:.22}),stalker:new THREE.MeshStandardMaterial({color:0xb79a52,emissive:0x6c4b16,emissiveIntensity:.48,roughness:.2}),spitter:new THREE.MeshStandardMaterial({color:0xc6a343,emissive:0x77601a,emissiveIntensity:.55,roughness:.2})},pupil:new THREE.MeshStandardMaterial({color:0x080707,roughness:.18}),spit:new THREE.MeshStandardMaterial({color:0x8a9c38,emissive:0x53621a,emissiveIntensity:.9,roughness:.28,metalness:.04})};
 monsterSpitGeometry=new THREE.SphereGeometry(.17,14,12);monsterSpitMaterial=monsterMaterials.spit;
}
function createMonsterHUD(){
 if(monsterHealthFill)return;
 const hud=$('hud');if(!hud)return;
 const box=document.createElement('div');box.id='monsterHUD';
 box.innerHTML='<div class="vh-top"><span class="vh-ico">&#9829;</span><span class="vh-label">VITALS</span><span class="vh-val">100</span></div><div class="vh-bar"><i class="vh-trail"></i><i class="vh-fill"></i><span class="vh-ticks"></span></div><div class="lv-row" style="display:flex;align-items:center;gap:9px;margin-top:-2px"><span style="font-size:11px;font-weight:800;letter-spacing:.14em;color:#8fc4ff;white-space:nowrap">LV <b class="lv-num" style="font-size:14px;color:#fff">1</b></span><div style="position:relative;flex:1;height:8px;border-radius:4px;background:rgba(255,255,255,.1);overflow:hidden;box-shadow:inset 0 1px 4px rgba(0,0,0,.55)"><i class="lv-fill" style="position:absolute;left:0;top:0;bottom:0;width:0;background:linear-gradient(90deg,#2f6dff,#7fc0ff);box-shadow:0 0 10px rgba(80,150,255,.6);transition:width .3s ease"></i></div></div>';
 ($('topRight')||hud).appendChild(box);
 monsterHealthFill=box.querySelector('.vh-fill');monsterHealthText=box.querySelector('.vh-val');monsterThreatText=box.querySelector('.vh-meta');
 monsterHurtFlash=document.createElement('div');monsterHurtFlash.style.cssText='position:fixed;inset:0;z-index:2;pointer-events:none;opacity:0;background:radial-gradient(ellipse at center,transparent 38%,rgba(150,10,10,.45) 115%);transition:opacity .08s;';$('screen').appendChild(monsterHurtFlash);updateMonsterHUD();
}
function updateMonsterHUD(){
 const box=document.getElementById('monsterHUD'),hp=Math.max(0,playerHealth);
 const hpPct=hp/UP.maxHp*100;if(monsterHealthFill)monsterHealthFill.style.width=hpPct+'%';
 if(monsterHealthText)monsterHealthText.textContent=Math.ceil(hp);
 if(box){box.dataset.lvl=hpPct<30?'low':hpPct<60?'mid':'hi';const t=box.querySelector('.vh-trail'),vt=box.querySelector('.vt'),vs=box.querySelector('.vs');
  if(t)t.style.width=hpPct+'%';if(vt)vt.textContent=monsters.filter(m=>m.alive).length;if(vs)vs.textContent=monsterKills;}
 try{waveHudUpdate();}catch(e){}
}
// weapon list: the active weapon is shown as a black icon, plus the key that switches to the other one
function weaponHudUpdate(){
 const sw=document.getElementById('wSword'),bw=document.getElementById('wBow');if(!sw||!bw)return;
 const isBow=weapon==='bow';
 if(sw._bow!==isBow){sw._bow=isBow;sw.classList.toggle('active',!isBow);bw.classList.toggle('active',isBow);
  document.getElementById('weaponHint').innerHTML=isBow?'<kbd>'+keyLabel('sword')+'</kbd> SWITCH TO SWORD':'<kbd>'+keyLabel('bow')+'</kbd> SWITCH TO BOW';}
 const f=document.getElementById('bowFill'),m=document.getElementById('wMeter');if(f&&m)m.style.width=isBow?(f.style.width||'0'):'0';
}
function monsterMesh(m,parent,geometry,material,x,y,z,sx,sy,sz,rx=0,ry=0,rz=0,casts=false){
 const mesh=new THREE.Mesh(geometry,material);mesh.position.set(x,y,z);mesh.scale.set(sx,sy,sz);mesh.rotation.set(rx,ry,rz);mesh.castShadow=casts;mesh.receiveShadow=false;mesh.userData.monster=m;parent.add(mesh);m.hitMeshes.push(mesh);monsterHitMeshes.push(mesh);if(m.meshBucket==='body')m.bodyMeshes.push(mesh);else if(m.meshBucket==='head')m.headMeshes.push(mesh);return mesh;
}
function monsterFlesh(m,parent,x,y,z,sx,sy,sz,material=m.skinMat,casts=false){return monsterMesh(m,parent,monsterOrganicGeometry,material,x,y,z,sx,sy,sz,0,0,0,casts);}
function monsterCone(m,parent,material,x,y,z,r,h,rx=0,ry=0,rz=0){return monsterMesh(m,parent,m.coneGeometry,material,x,y,z,r,h,r,rx,ry,rz,false);}
function finalizeMonsterRig(m){
 const oldRig=m.rig,hips=new THREE.Group();hips.name='mixamorigHips';hips.position.y=1.02;m.root.add(hips);
 const spine=new THREE.Group();spine.name='mixamorigSpine';spine.position.y=.30;hips.add(spine);
 const spine1=new THREE.Group();spine1.name='mixamorigSpine1';spine1.position.y=.29;spine.add(spine1);
 const spine2=new THREE.Group();spine2.name='mixamorigSpine2';spine2.position.y=.29;spine1.add(spine2);
 const neck=new THREE.Group();neck.name='mixamorigNeck';neck.position.y=.25;spine2.add(neck);
 const head=new THREE.Group();head.name='mixamorigHead';head.position.y=.28;neck.add(head);
 m.bone={hips,spine,spine1,spine2,neck,head};
 m.root.updateMatrixWorld(true);
 // Pelvis masses follow the hips, the belly follows the lower spine, chest/shoulders follow the upper spine, so the torso can really bend.
 for(const mesh of m.bodyMeshes){const y=mesh.position.y;(y<1.18?hips:y<1.5?spine:spine2).attach(mesh);}
 for(const mesh of m.headMeshes)head.attach(mesh);
 for(const a of m.arms){const shoulder=new THREE.Group();shoulder.name=a.side<0?'mixamorigLeftShoulder':'mixamorigRightShoulder';shoulder.position.set(a.side*.5,.01,0);spine2.add(shoulder);shoulder.updateMatrixWorld(true);shoulder.attach(a.upper);a.upper.name=a.side<0?'mixamorigLeftArm':'mixamorigRightArm';a.fore.name=a.side<0?'mixamorigLeftForeArm':'mixamorigRightForeArm';a.hand.name=a.side<0?'mixamorigLeftHand':'mixamorigRightHand';}
 for(const l of m.legs){hips.updateMatrixWorld(true);hips.attach(l.upper);l.upper.name=l.side<0?'mixamorigLeftUpLeg':'mixamorigRightUpLeg';l.lower.name=l.side<0?'mixamorigLeftLeg':'mixamorigRightLeg';l.foot.name=l.side<0?'mixamorigLeftFoot':'mixamorigRightFoot';}
 m.root.remove(oldRig);m.rig=hips;m.root.updateMatrixWorld(true);
}function buildMonsterArm(m,side){
 const sideName=side<0?'Left':'Right',L=m.cfg.arm,upper=new THREE.Group();upper.name='mixamorig'+sideName+'Arm';upper.position.set(side*.5,1.91,0);m.rig.add(upper);
 monsterFlesh(m,upper,0,-.25*L,0,.185,.33*L,.19);monsterFlesh(m,upper,0,-.47*L,.015,.14,.16,.145,m.darkMat);
 const fore=new THREE.Group();fore.name='mixamorig'+sideName+'ForeArm';fore.position.y=-.49*L;upper.add(fore);monsterFlesh(m,fore,0,-.24*L,.035,.15,.34*L,.16);monsterFlesh(m,fore,0,-.48*L,.08,.115,.13,.125,m.darkMat);
 const hand=new THREE.Group();hand.name='mixamorig'+sideName+'Hand';hand.position.set(0,-.55*L,.12);fore.add(hand);monsterFlesh(m,hand,0,0,0,.135,.13,.12,m.skinMat);for(let i=-1;i<=1;i++)monsterCone(m,hand,m.clawMat,i*.068,-.08*L,.10,.033,.21,Math.PI/2,0,i*.12);
 m.arms.push({upper,fore,hand,side});
}
function buildMonsterLeg(m,side){
 const sideName=side<0?'Left':'Right',upper=new THREE.Group();upper.name='mixamorig'+sideName+'UpLeg';upper.position.set(side*.225,1.02,0);m.rig.add(upper);monsterFlesh(m,upper,0,-.26,0,.225,.35,.24);monsterFlesh(m,upper,0,-.48,.015,.17,.14,.18,m.darkMat);
 const lower=new THREE.Group();lower.name='mixamorig'+sideName+'Leg';lower.position.y=-.51;upper.add(lower);monsterFlesh(m,lower,0,-.24,.015,.17,.34,.18);monsterFlesh(m,lower,0,-.48,.10,.18,.14,.29,m.darkMat);
 const foot=new THREE.Group();foot.name='mixamorig'+sideName+'Foot';foot.position.set(0,-.52,.10);lower.add(foot);for(let i=-1;i<=1;i++)monsterCone(m,foot,m.clawMat,i*.09,0,.16,.027,.14,Math.PI/2,0,i*.16);
 m.legs.push({upper,lower,foot,side});
}
const MONSTER_SIZE=1.5;   // size multiplier for every monster (also scales attack reach so bigger bodies still hit from their edge)
function createMonster(type,x,z){
 const configs={brute:{name:'ASHEN BRUTE',scale:1.22*MONSTER_SIZE,hp:230,speed:3.795,damage:24,range:2.35*MONSTER_SIZE,cooldown:1.7,arm:1.05,skin:'brute'},stalker:{name:'NIGHT STALKER',scale:.92*MONSTER_SIZE,hp:105,speed:8.05,damage:13,range:1.75*MONSTER_SIZE,cooldown:.82,arm:1.34,skin:'stalker'},spitter:{name:'MIRE SPITTER',scale:1.04*MONSTER_SIZE,hp:145,speed:4.14,damage:17,range:2*MONSTER_SIZE,cooldown:2.35,arm:1.12,skin:'spitter'}};
 const cfg=configs[type],root=new THREE.Group(),rig=new THREE.Group(),m={type,cfg,root,rig,alive:true,dead:false,hp:cfg.hp,maxHp:cfg.hp,phase:Math.random()*6.28,attackCooldown:.8+Math.random(),attackAnim:0,attackSide:1,recoil:0,hitMeshes:[],bodyMeshes:[],headMeshes:[],meshBucket:'body',arms:[],legs:[],lastSwordSerial:0,attackSerial:0,deadTimer:0,spawn:new THREE.Vector3(x,.035,z)};
 m.skinMat=monsterMaterials.skin[type];m.darkMat=monsterMaterials.dark;m.mouthMat=monsterMaterials.mouth;m.socketMat=monsterMaterials.socket;m.toothMat=monsterMaterials.tooth;m.clawMat=monsterMaterials.claw;m.coneGeometry=new THREE.ConeGeometry(1,1,7);m.eyeMat=monsterMaterials.eyes[type];
 root.position.copy(m.spawn);root.scale.setScalar(cfg.scale);scene.add(root);root.add(rig);m.rig=rig;
 // Dense, uneven muscle masses form a living silhouette rather than exposed ribs or a toy skeleton.
 monsterFlesh(m,rig,0,1.02,0,.39,.28,.30);monsterFlesh(m,rig,0,1.34,-.005,.39,.43,.29);monsterFlesh(m,rig,0,1.69,0,.50,.48,.32,m.skinMat,true);monsterFlesh(m,rig,0,1.92,-.015,.43,.31,.30);
 for(const side of [-1,1]){monsterFlesh(m,rig,side*.245,1.78,.19,.255,.245,.22);monsterFlesh(m,rig,side*.48,1.94,0,.25,.29,.26);}
 m.meshBucket='head';monsterFlesh(m,rig,0,2.18,0,.18,.25,.18);monsterFlesh(m,rig,0,2.43,.025,.275,.32,.245,m.skinMat,true);monsterFlesh(m,rig,0,2.22,.11,.205,.16,.21,m.skinMat);
 monsterMesh(m,rig,monsterOrganicGeometry,m.mouthMat,0,2.315,.257,.155,.083,.045);
 for(const side of [-1,1]){monsterFlesh(m,rig,side*.112,2.49,.225,.094,.075,.045,m.socketMat);monsterFlesh(m,rig,side*.112,2.49,.266,.052,.047,.025,m.eyeMat);monsterFlesh(m,rig,side*.112,2.49,.289,.021,.03,.012,monsterMaterials.pupil);monsterFlesh(m,rig,side*.12,2.57,.22,.115,.035,.062,m.skinMat);}
 for(let i=0;i<5;i++){const xx=(i-2)*.052;monsterCone(m,rig,m.toothMat,xx,2.335,.285,.021,.073,0,0,Math.PI);if(i!==2)monsterCone(m,rig,m.toothMat,xx,2.29,.285,.018,.06,0,0,0);}
 m.meshBucket='body';// Type-specific silhouettes, surface details and coloration.
 if(type==='brute'){
  for(const side of [-1,1]){monsterMesh(m,rig,new THREE.IcosahedronGeometry(1,1),monsterMaterials.bruteArmor,side*.47,2.05,-.01,.31,.24,.29,0,0,side*-.16);monsterCone(m,rig,monsterMaterials.bruteArmor,side*.16,2.77,-.015,.105,.42,-.35,0,side*-.22);}
  monsterFlesh(m,rig,-.12,1.65,.286,.18,.12,.035,monsterMaterials.scar);monsterFlesh(m,rig,-.04,1.61,.31,.15,.018,.018,monsterMaterials.dark);
 }else if(type==='stalker'){
  for(let i=0;i<5;i++)monsterCone(m,rig,monsterMaterials.stalkerPlate,0,2.21-i*.16,-.285,.075-i*.006,.32,-.72,0,0);
  for(const side of [-1,1])monsterCone(m,rig,monsterMaterials.stalkerPlate,side*.18,2.68,.005,.055,.24,-.15,0,side*.2);
  monsterFlesh(m,rig,.24,1.5,.20,.07,.25,.08,monsterMaterials.scar, false);
 }else{
  monsterFlesh(m,rig,0,1.42,.17,.30,.33,.24,monsterMaterials.spitterSack,true);monsterFlesh(m,rig,0,2.13,.235,.21,.17,.16,monsterMaterials.spitterSack);
  for(const side of [-1,1]){monsterFlesh(m,rig,side*.27,1.78,-.24,.19,.26,.20,monsterMaterials.spitterSack);monsterFlesh(m,rig,side*.28,1.80,-.07,.075,.17,.075,monsterMaterials.scar);}
  for(let i=0;i<4;i++)monsterFlesh(m,rig,(i%2?1:-1)*(.20+(i%3)*.035),1.50+(i>>1)*.18,-.34,.075,.09,.07,monsterMaterials.spitterSack);
 }
 m.meshBucket=null;for(const side of [-1,1]){buildMonsterArm(m,side);buildMonsterLeg(m,side);}
 m.name=cfg.name;finalizeMonsterRig(m);monsters.push(m);root.updateMatrixWorld(true);mnInit(m);root.updateMatrixWorld(true);return m;
}
function buildMonsters(){
 if(monsters.length)return;setupMonsterMaterials();createMonsterHUD();
 const defs=[['stalker',0,96],['brute',-9,86],['spitter',9,103],['brute',-88,60],['stalker',88,60],['spitter',0,-60]];
 for(const [type,x,z] of defs)createMonster(type,x,z);monsters.forEach((m,i)=>startWallEntry(m,i));updateMonsterHUD();
}
let _mnObst=null,_mnObstN=-1;
function monsterSpotFree(x,z,r){
 if(Math.hypot(x,z)>WORLD.wallRadius-5)return false;
 if(_mnObstN!==colliders.length){_mnObst=colliders.filter(c=>c.kind!=='roof'&&c.kind!=='gable'&&c.top>=.4);_mnObstN=colliders.length;}
 for(const c of _mnObst){const cx=THREE.MathUtils.clamp(x,c.x-c.halfX,c.x+c.halfX),cz=THREE.MathUtils.clamp(z,c.z-c.halfZ,c.z+c.halfZ);const dx=x-cx,dz=z-cz;if(dx*dx+dz*dz<r*r)return false;}
 return true;
}

// ===================== MONSTER PATH FINDING =====================
// The old steering only slid along a wall, so monsters got stuck in corners, between buildings and in dead ends. Now the static obstacles are rasterised
// once into a grid; when a building is between a monster and its target (grid line-of-sight blocked) the monster follows an A* route around it
// (re-planned every second or when the target moved, at most MNP.perFrame plans per frame). The old local steering is still the fallback.
// If a monster still makes no progress it is re-routed, and as a last resort pushed out to the nearest free spot. Tweak live: MNP.R (clearance, m)  MNP.replan (s)
const MNP={cell:1,R:.9,N:0,org:0,blocked:null,n:-1,budget:1,perFrame:1,replan:1.1,g:null,par:null,seen:null,stamp:1,maxExp:60000};
function mnGridBuild(){
 if(_mnObstN!==colliders.length||!_mnObst){_mnObst=colliders.filter(c=>c.kind!=='roof'&&c.kind!=='gable'&&c.top>=.4);_mnObstN=colliders.length;}
 const C=MNP.cell,half=WORLD.wallRadius+4,N=Math.ceil(half*2/C);MNP.N=N;MNP.org=-half;MNP.blocked=new Uint8Array(N*N);
 const B=MNP.blocked,lim=WORLD.wallRadius-5;
 for(let j=0;j<N;j++)for(let i=0;i<N;i++){const x=MNP.org+(i+.5)*C,z=MNP.org+(j+.5)*C;if(x*x+z*z>lim*lim)B[j*N+i]=1;}
 for(const c of _mnObst){
  const i0=Math.max(0,Math.floor((c.x-c.halfX-MNP.R-MNP.org)/C)),i1=Math.min(N-1,Math.floor((c.x+c.halfX+MNP.R-MNP.org)/C));
  const j0=Math.max(0,Math.floor((c.z-c.halfZ-MNP.R-MNP.org)/C)),j1=Math.min(N-1,Math.floor((c.z+c.halfZ+MNP.R-MNP.org)/C));
  for(let j=j0;j<=j1;j++)for(let i=i0;i<=i1;i++){
   const x=MNP.org+(i+.5)*C,z=MNP.org+(j+.5)*C,cx=Math.max(c.x-c.halfX,Math.min(c.x+c.halfX,x)),cz=Math.max(c.z-c.halfZ,Math.min(c.z+c.halfZ,z));
   const dx=x-cx,dz=z-cz;if(dx*dx+dz*dz<MNP.R*MNP.R)B[j*N+i]=1;}
 }
 if(!MNP.g||MNP.g.length!==N*N){MNP.g=new Float32Array(N*N);MNP.par=new Int32Array(N*N);MNP.seen=new Uint32Array(N*N);MNP.stamp=1;}
 MNP.n=colliders.length;
}
function mnGrid(){if(MNP.n!==colliders.length||!MNP.blocked)mnGridBuild();return MNP.blocked;}
const mnCell=(x,z)=>{const N=MNP.N,i=Math.floor((x-MNP.org)/MNP.cell),j=Math.floor((z-MNP.org)/MNP.cell);return(i<0||j<0||i>=N||j>=N)?-1:j*N+i;};
function mnBlockedAt(x,z){const k=mnCell(x,z);return k<0||MNP.blocked[k]===1;}
// grid line of sight; the first `skip` metres (monster standing in the safety margin of a wall) and the last `tail` metres (target hugging a wall) are ignored
function mnLOS(x0,z0,x1,z1,skip,tail){
 const dx=x1-x0,dz=z1-z0,d=Math.hypot(dx,dz);if(d<.01)return true;const st=MNP.cell*.5,n=Math.ceil(d/st),ux=dx/d,uz=dz/d;
 for(let i=1;i<=n;i++){const t=Math.min(d,i*st);if(t<skip||t>d-tail)continue;if(mnBlockedAt(x0+ux*t,z0+uz*t))return false;}
 return true;
}
function mnNearestFree(k){   // nearest unblocked cell around k (spiral), or -1
 const N=MNP.N,B=MNP.blocked;if(k<0)return -1;if(!B[k])return k;const ci=k%N,cj=(k-ci)/N;
 for(let r=1;r<=12;r++){let best=-1,bd=1e9;for(let j=cj-r;j<=cj+r;j++)for(let i=ci-r;i<=ci+r;i++){if(Math.max(Math.abs(i-ci),Math.abs(j-cj))!==r||i<0||j<0||i>=N||j>=N)continue;const q=j*N+i;if(B[q])continue;const d=(i-ci)*(i-ci)+(j-cj)*(j-cj);if(d<bd){bd=d;best=q;}}if(best>=0)return best;}
 return -1;
}
const _mnH={f:[],n:[]};
function mnHPush(f,n){const F=_mnH.f,Nn=_mnH.n;let i=F.length;F.push(f);Nn.push(n);while(i>0){const p=(i-1)>>1;if(F[p]<=f)break;F[i]=F[p];Nn[i]=Nn[p];i=p;}F[i]=f;Nn[i]=n;}
function mnHPop(){const F=_mnH.f,Nn=_mnH.n,top=Nn[0],lf=F.pop(),ln=Nn.pop(),L=F.length;if(L){let i=0;for(;;){let c=i*2+1;if(c>=L)break;if(c+1<L&&F[c+1]<F[c])c++;if(F[c]>=lf)break;F[i]=F[c];Nn[i]=Nn[c];i=c;}F[i]=lf;Nn[i]=ln;}return top;}
// returns an array of [x,z] waypoints from (sx,sz) to (gx,gz), or null
function mnFindPath(sx,sz,gx,gz){
 mnGrid();const N=MNP.N,B=MNP.blocked,C=MNP.cell;
 const s=mnNearestFree(mnCell(sx,sz)),g=mnNearestFree(mnCell(gx,gz));if(s<0||g<0)return null;
 if(s===g)return[[MNP.org+((g%N)+.5)*C,MNP.org+(((g-g%N)/N)+.5)*C]];
 const G=MNP.g,P=MNP.par,S=MNP.seen,st=++MNP.stamp,gi=g%N,gj=(g-gi)/N;_mnH.f.length=0;_mnH.n.length=0;
 const hf=(i,j)=>{const a=Math.abs(i-gi),b=Math.abs(j-gj);return(Math.max(a,b)+.4142*Math.min(a,b))*1.15;};
 const si=s%N,sj=(s-si)/N;G[s]=0;P[s]=-1;S[s]=st;mnHPush(hf(si,sj),s);let exp=0,found=false;
 const closed=new Set();
 while(_mnH.n.length&&exp<MNP.maxExp){
  const k=mnHPop();if(closed.has(k))continue;closed.add(k);exp++;if(k===g){found=true;break;}
  const ki=k%N,kj=(k-ki)/N,gk=G[k];
  for(let dj=-1;dj<=1;dj++)for(let di=-1;di<=1;di++){
   if(!di&&!dj)continue;const ni=ki+di,nj=kj+dj;if(ni<0||nj<0||ni>=N||nj>=N)continue;const q=nj*N+ni;if(B[q])continue;
   if(di&&dj&&(B[kj*N+ni]||B[nj*N+ki]))continue;   // no cutting corners
   const ng=gk+(di&&dj?1.4142:1);if(S[q]===st&&G[q]<=ng)continue;S[q]=st;G[q]=ng;P[q]=k;mnHPush(ng+hf(ni,nj),q);}
 }
 if(!found)return null;
 const cells=[];for(let k=g;k>=0;k=P[k])cells.push(k);cells.reverse();
 const pts=cells.map(k=>{const i=k%N,j=(k-i)/N;return[MNP.org+(i+.5)*C,MNP.org+(j+.5)*C];});
 // string pulling: drop every waypoint that can be skipped with a clear line of sight
 const out=[];let a=0;
 while(a<pts.length-1){let b=pts.length-1;while(b>a+1&&!mnLOS(pts[a][0],pts[a][1],pts[b][0],pts[b][1],0,0))b--;out.push(pts[b]);a=b;}
 return out;
}
function mnUnstick(m){   // embedded in an obstacle: move to the closest free spot
 const p=m.root.position,r=.48*m.cfg.scale;if(monsterSpotFree(p.x,p.z,r))return;
 for(let d=1;d<=14;d+=1)for(let a=0;a<12;a++){const th=a/12*6.2832,x=p.x+Math.cos(th)*d,z=p.z+Math.sin(th)*d;if(monsterSpotFree(x,z,r)){p.x=x;p.z=z;return;}}
}
// Steering: walk straight at the target while the way ahead is clear; when a building blocks it, slide along the obstacle (the side that
// leads toward the target, kept for a while so they don't jitter) until the straight line opens up again.
function moveMonsterToward(m,tx,tz,dt){
 const p=m.root.position,dx=tx-p.x,dz=tz-p.z,dist=Math.hypot(dx,dz);if(dist<.01)return false;
 const step=Math.min(m.cfg.speed*dt,Math.max(0,dist-m.cfg.range*.78));if(step<.001)return false;
 const r=.48*m.cfg.scale,base=Math.atan2(dx,dz),look=Math.max(step*2,r*2.4+.6);
 const free=(a,L)=>monsterSpotFree(p.x+Math.sin(a)*L,p.z+Math.cos(a)*L,r);
 const clear=a=>free(a,look*.5)&&free(a,look);   // look ahead, so they turn before touching the wall
 const go=a=>{const nx=p.x+Math.sin(a)*step,nz=p.z+Math.cos(a)*step;if(!monsterSpotFree(nx,nz,r))return false;p.x=nx;p.z=nz;return true;};
 // ---- stuck watchdog: no real progress for ~.8 s while trying to walk -> re-plan the route, and finally pull the monster out of whatever it is stuck in
 {const S=m.stk||(m.stk={x:p.x,z:p.z,t:0,n:0});S.t+=dt;if(S.t>.8){const mv=Math.hypot(p.x-S.x,p.z-S.z);S.x=p.x;S.z=p.z;S.t=0;
   if(mv<m.cfg.speed*.8*.3){S.n++;m.path=null;m.forcePlan=true;m.detour=null;if(S.n>=3){try{mnUnstick(m);}catch(e){}}}else S.n=0;}}
 // ---- A* route around buildings
 try{
  mnGrid();
  const blockedLOS=!mnLOS(p.x,p.z,tx,tz,1.2,1.6);
  if(blockedLOS||m.forcePlan||m.path){
   if(!blockedLOS&&!m.forcePlan)m.path=null;   // the way is open again
   else{
    if(m.path){m.pathT+=dt;if(m.pathT>MNP.replan&&Math.hypot(tx-m.pgx,tz-m.pgz)>2.5)m.path=null;else if(m.pathT>MNP.replan*3)m.path=null;}
    if(!m.path&&MNP.budget>0){MNP.budget--;const pa=mnFindPath(p.x,p.z,tx,tz);m.pathT=0;m.pgx=tx;m.pgz=tz;if(pa&&pa.length){m.path=pa;m.pi=0;m.detour=null;}else{m.forcePlan=false;}}
    if(m.path){
     while(m.pi<m.path.length&&Math.hypot(m.path[m.pi][0]-p.x,m.path[m.pi][1]-p.z)<.8)m.pi++;
     if(m.pi>=m.path.length){m.path=null;m.forcePlan=false;}
     else{const w=m.path[m.pi],a=Math.atan2(w[0]-p.x,w[1]-p.z);
      for(const d of[0,.35,-.35,.7,-.7,1.1,-1.1,1.6,-1.6]){if(go(a+d))return true;}
      m.path=null;}   // could not move toward the waypoint: re-plan next time
    }
   }
  }
 }catch(e){if(!moveMonsterToward.warned){moveMonsterToward.warned=true;console.error('[monster path]',e);}}
 let D=m.detour;
 if(clear(base)){if(D){D.free=(D.free||0)+dt;if(D.free>.5)m.detour=null;}if(go(base))return true;}
 if(!D){
  const L=2.2*r+1,a1=base+Math.PI/2,a2=base-Math.PI/2,dd=a=>free(a,r+.6)?Math.hypot(tx-(p.x+Math.sin(a)*L),tz-(p.z+Math.cos(a)*L)):1e9,d1=dd(a1),d2=dd(a2);
  let sd=d1<=d2?1:-1;if(Math.abs(d1-d2)<.5&&Math.random()<.5)sd=-sd;
  D=m.detour={side:sd,t:0,d0:dist,free:0};
 }
 D.free=0;D.t+=dt;
 if(D.t>3){if(dist>D.d0-2)D.side=-D.side;D.t=0;D.d0=dist;}   // no progress (dead end): try the other way around
 const ths=[.5,.8,1.1,1.45,1.8,2.2,2.7];
 for(const th of ths){const a=base+D.side*th;if(clear(a)&&go(a))return true;}
 for(const th of ths){if(go(base+D.side*th))return true;}
 D.side=-D.side;
 for(const th of ths){if(go(base+D.side*th))return true;}
 return false;
}
function removeMonsterFromArrowTargets(m){for(const mesh of m.hitMeshes){const i=monsterHitMeshes.indexOf(mesh);if(i>=0)monsterHitMeshes.splice(i,1);}}
// ===================== FLOATING DAMAGE NUMBERS ON MONSTERS (same style as the boss numbers) =====================
// The number pops up at the exact spot of the hit (arrows: the real impact point; sword / lunge / leap / slam / kick: the body point where the sparks appear)
// and floats up. Tweak live from the console, e.g.  MNUM.on=false  MNUM.size=26  MNUM.rise=100
const MNUM={on:true,pt:null,live:0,max:24,size:1,rise:80,dur:.85,style:false,v:null};
function mnumStyle(){if(MNUM.style)return;MNUM.style=true;const st=document.createElement('style');
 st.textContent='.mnNum{position:fixed;left:0;top:0;pointer-events:none;z-index:9;font-family:system-ui,Segoe UI,Arial,sans-serif;font-weight:900;line-height:1;white-space:nowrap;text-shadow:0 0 6px #000,0 0 2px #000,0 1px 0 #000;opacity:0;animation:mnNumPop var(--d,.85s) cubic-bezier(.15,.7,.3,1) forwards}'+
  '@keyframes mnNumPop{0%{opacity:0;transform:translate(calc(-50% + var(--dx,0px)),0) scale(.5)}14%{opacity:1;transform:translate(calc(-50% + var(--dx,0px)),calc(var(--rise,80px)*-.18)) scale(1.35)}35%{opacity:1;transform:translate(calc(-50% + var(--dx,0px)),calc(var(--rise,80px)*-.45)) scale(1)}100%{opacity:0;transform:translate(calc(-50% + var(--dx,0px)),calc(var(--rise,80px)*-1)) scale(.9)}}';
 document.head.appendChild(st);}
function mnumHitPos(m,kind){   // world position of the blow on the monster's body
 const sc=(m.cfg&&m.cfg.scale)||1,out=MNUM.v||(MNUM.v=new THREE.Vector3());
 if(kind==='arrow'&&MNUM.pt){out.copy(MNUM.pt);MNUM.pt=null;return out;}
 MNUM.pt=null;
 out.set(m.root.position.x,m.root.position.y+(1.2+Math.random()*.35)*sc,m.root.position.z);   // chest height, same spot as swordHitFx
 const dx=player.pos.x-out.x,dz=player.pos.z-out.z,l=Math.hypot(dx,dz)||1;out.x+=dx/l*.45*sc+(Math.random()-.5)*.35*sc;out.z+=dz/l*.45*sc+(Math.random()-.5)*.35*sc;   // pulled toward the player so it sits on the body surface
 return out;}
function mnumShow(pos,m,amount,kind,hp0,killed){
 if(!MNUM.on||!camera||MNUM.live>=MNUM.max)return;
 const val=Math.max(1,Math.round(amount>=9000?hp0:amount));   // instant-kill shockwaves show the health they removed, not 99999
 const p=pos.clone().project(camera);if(p.z>1||p.z<-1||Math.abs(p.x)>1.15||Math.abs(p.y)>1.15)return;
 mnumStyle();
 const x=(p.x*.5+.5)*innerWidth,y=(-p.y*.5+.5)*innerHeight,d=camera.position.distanceTo(pos),dscale=Math.max(.65,Math.min(1.15,26/Math.max(10,d)));
 const el=document.createElement('div');el.className='mnNum';el.textContent=String(val);
 el.style.color=killed?'#ff4a3a':val>=120?'#ff7a3a':'#ffd24a';
 el.style.fontSize=((17+Math.min(11,val/12))*dscale*MNUM.size*(killed?1.15:1)).toFixed(1)+'px';
 el.style.left=x.toFixed(1)+'px';el.style.top=y.toFixed(1)+'px';
 el.style.setProperty('--dx',((Math.random()-.5)*50).toFixed(1)+'px');el.style.setProperty('--rise',(MNUM.rise*dscale).toFixed(0)+'px');el.style.setProperty('--d',MNUM.dur+'s');
 MNUM.live++;let done=false;const fin=()=>{if(done)return;done=true;MNUM.live--;el.remove();};
 el.addEventListener('animationend',fin);setTimeout(fin,MNUM.dur*1000+400);
 document.body.appendChild(el);}
function damageMonster(m,amount,kind,quiet){
 if(!m||!m.alive)return;if(m.boss)return bossDamage(m,amount,kind,quiet);if(kind==='sword'){if(!quiet)sound('swordHit');if(amount<9000)amount=Math.round(amount*UP.swordMul*BAL.hpMul(WAVES.n));}if(kind==='arrow')amount=Math.round(amount*UP.bowMul*BAL.hpMul(WAVES.n));   // arrows: big damage (BAL.arrowBase + draw power * BAL.arrowPow), boosted by the ARROW DAMAGE upgrade
 const _mnHp0=m.hp,_mnPt=mnumHitPos(m,kind);m.hp=Math.max(0,m.hp-amount);m.recoil=.2;if(!quiet)sound('monsterHurt');mnumShow(_mnPt,m,amount,kind,_mnHp0,m.hp<=0);
 if(m.hp<=0){playMonsterAsset('monsterDie',m);xpGain(m);m.alive=false;m.dead=true;m.climb=null;m.roof=null;m.deathY0=Math.max(0,m.root.position.y-m.spawn.y);m.deathVy=0;if(!mnRagdollStart(m,kind,amount)){if(m.down)mnBeginDeathLying(m);else mnBeginDeath(m);mnKnock(m,(kind==='arrow'?1.4:2.6)/m.cfg.scale);}monsterKills++;removeMonsterFromArrowTargets(m);}
 else mnHitReact(m,amount,kind);
 updateMonsterHUD();
}
function damagePlayer(amount,source){if(monsterRespawnTimer>0||playerHurtCooldown>0)return;if(player.block){blockHit(source);return;}playerHurtCooldown=.62;playerHealth=Math.max(0,playerHealth-amount*.8);if(monsterHurtFlash)monsterHurtFlash.style.opacity='.9';if(source){const dx=player.pos.x-source.x,dz=player.pos.z-source.z,l=Math.hypot(dx,dz)||1;player.vel.x+=dx/l*3.2;player.vel.z+=dz/l*3.2;if(player.grounded){player.grounded=false;player.vel.y=Math.max(player.vel.y,2.1);}}
 if(playerHealth<=0){playerHealth=0;startPlayerDeath();}updateMonsterHUD();}
// ---- Player death: play the "Dying Backwards" animation, then show the defeat menu (reason: the player died)
function startPlayerDeath(){
 const D=playerDeath;if(D.active)return;
 D.active=true;D.started=false;D.shown=false;D.t=0;D.wasThird=thirdPerson;
 monsterRespawnTimer=1e9;   // the monsters stop hunting the player until the run is restarted
 player.slam=null;player.kick=null;player.dash=null;player.fallRoll=null;try{lungeReset();}catch(e){}try{detachAll(false);}catch(e){}try{stopAim();}catch(e){}
 player.sliding=false;player.climbing=false;player.mantle=null;player.onWall=false;player.postFlight=false;player.jumpBuffer=0;
 for(const k in keys)keys[k]=false;
 if(!thirdPerson){thirdPerson=true;cameraPositionInitialized=false;try{applyCharacterViewMode();}catch(e){}}   // the fall must be visible
}
function playerDeathTick(dt){
 const D=playerDeath,A=erikaAnim;
 for(const k in keys)keys[k]=false;   // no input while dying
 const damp=Math.exp(-6*dt);player.vel.x*=damp;player.vel.z*=damp;player.jumpBuffer=0;
 player.pitch+=(-.32-player.pitch)*(1-Math.exp(-2.5*dt));   // camera rises a little so the body stays in view
 D.t+=dt;
 const dur=(A.ready&&A.deathAct&&A.durs.Death)?A.durs.Death:1.4;
 if(!D.shown&&D.t>=dur+.4){D.shown=true;showGameOver('player');}
}
function playerDeathReset(){
 const D=playerDeath;if(!D.active)return;
 D.active=false;D.started=false;D.shown=false;D.t=0;
 if(FIRST_PERSON_ENABLED&&!D.wasThird&&thirdPerson){thirdPerson=false;cameraPositionInitialized=false;try{applyCharacterViewMode();}catch(e){}}
}
// ---- slimy green spit: a wobbling, stretched glob with dripping blobs and a glowing trail; splashes into droplets on impact
let _slimeMat=null,_slimeGeo=null,_slimeDripGeo=null;
function spitGlob(){
 if(!_slimeMat){
  _slimeMat=new THREE.MeshStandardMaterial({color:0x4fb21e,emissive:0x1d6a0a,emissiveIntensity:.75,roughness:.12,metalness:.05,transparent:true,opacity:.93});
  _slimeGeo=new THREE.SphereGeometry(.2,18,14);_slimeDripGeo=new THREE.SphereGeometry(.07,10,8);
 }
 const g=new THREE.Group(),geo=_slimeGeo.clone(),base=geo.attributes.position.array.slice(),blob=new THREE.Mesh(geo,_slimeMat);blob.castShadow=false;g.add(blob);
 const drips=[];for(let i=0;i<4;i++){const d=new THREE.Mesh(_slimeDripGeo,_slimeMat);g.add(d);drips.push(d);}
 const tex=(typeof hfxTexSafe==='function')?hfxTexSafe():null;
 const glow=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,color:0x59e02a,transparent:true,opacity:.55,depthWrite:false,blending:THREE.AdditiveBlending,fog:false}));glow.scale.setScalar(.9);g.add(glow);
 g.userData.slime={blob,geo,base,drips,t:Math.random()*10};return g;
}
function spitGlobUpdate(p,dt){
 const g=p.mesh,S=g.userData.slime;if(!S)return;S.t+=dt;
 const v=p.vel,sp=v.length();if(sp>.01){g.quaternion.setFromUnitVectors(_skFwd,_skV1.copy(v).divideScalar(sp));}   // local +z = flight direction
 const pos=S.geo.attributes.position,b=S.base,t=S.t;
 for(let i=0;i<pos.count;i++){const x=b[i*3],y=b[i*3+1],z=b[i*3+2],w=1+.16*Math.sin(x*22+t*17)*Math.sin(y*19-t*13)+.1*Math.sin(z*25+t*21);pos.setXYZ(i,x*w,y*w,z*w*1.55);}   // stretched along the flight, surface wobbling like jelly
 pos.needsUpdate=true;S.geo.computeVertexNormals();
 for(let i=0;i<S.drips.length;i++){const d=S.drips[i],k=i+1;d.position.set(Math.sin(t*9+i*2)*.05,-.04*k+Math.sin(t*12+i)*.03,-.26-k*.16);d.scale.setScalar(Math.max(.25,1-k*.2)*(1+.2*Math.sin(t*14+i)));}
 if(HFX.ready&&Math.random()<.7){_skV2.copy(g.position);_dfx.v.set((Math.random()-.5)*1.5,-.5-Math.random()*1.5,(Math.random()-.5)*1.5);const q=dashSpark(_skV2,_dfx.v,.35+Math.random()*.25,.07+Math.random()*.07,Math.random()<.5?0x5ad22a:0x2f8a14);q.grav=1;}
}
function spitSplat(pos){
 if(!HFX.ready)return;
 hfxPut(HFX.flashes,pos,.18,1.6,4,0x66e030);hfxPut(HFX.rings,pos,.3,.3,3.5,0x3fae1a);
 for(let i=0;i<22;i++){const th=Math.random()*6.283,sp=2+Math.random()*5;_dfx.v.set(Math.cos(th)*sp,1+Math.random()*4,Math.sin(th)*sp);const q=dashSpark(pos,_dfx.v,.4+Math.random()*.4,.09+Math.random()*.11,i%3?0x4fc023:0x2a7a10);q.grav=1;}
}
function launchMonsterSpit(m){
 const forward=new THREE.Vector3(0,0,1).applyAxisAngle(new THREE.Vector3(0,1,0),m.root.rotation.y),from=new THREE.Vector3(m.root.position.x,m.root.position.y+(m.model?1.85:2.2)*m.cfg.scale,m.root.position.z).addScaledVector(forward,(m.model?.35:.5)*m.cfg.scale),to=new THREE.Vector3(player.pos.x,player.pos.y+1.05,player.pos.z),vel=to.sub(from).normalize().multiplyScalar(18);
 const mesh=spitGlob();mesh.position.copy(from);scene.add(mesh);monsterProjectiles.push({mesh,vel,life:3.5,damage:17});m.attackSerial++;
}
function monsterProjectileBlocked(a,b){
 for(const c of colliders){if(c.kind==='roof'||c.kind==='gable'||c.top<.5)continue;for(let j=1;j<=3;j++){const t=j/3,x=THREE.MathUtils.lerp(a.x,b.x,t),y=THREE.MathUtils.lerp(a.y,b.y,t),z=THREE.MathUtils.lerp(a.z,b.z,t);if(y>0&&y<c.top&&Math.abs(x-c.x)<c.halfX&&Math.abs(z-c.z)<c.halfZ)return true;}}
 return false;
}
function updateMonsterProjectiles(dt){
 const target=new THREE.Vector3(player.pos.x,player.pos.y+1.05,player.pos.z);
 for(let i=monsterProjectiles.length-1;i>=0;i--){const p=monsterProjectiles[i],from=p.mesh.position.clone();p.life-=dt;p.vel.y-=2.2*dt;p.mesh.position.addScaledVector(p.vel,dt);spitGlobUpdate(p,dt);
  const hitPlayer=p.mesh.position.distanceTo(target)<.88,blocked=monsterProjectileBlocked(from,p.mesh.position);
  if(hitPlayer){damagePlayer(p.damage,from);p.life=0;spitSplat(p.mesh.position);}else if(blocked||p.mesh.position.y<.05){p.life=0;spitSplat(p.mesh.position);}
  if(p.life<=0){scene.remove(p.mesh);if(p.mesh.userData.slime)p.mesh.userData.slime.geo.dispose();monsterProjectiles.splice(i,1);}
 }
}
function updateMonsterSwordHits(){
 const A=erikaAnim,action=A.attackAction;if(!action||!A.attackSerial||action.time<.1||action.time>1.25)return;
 const fx=-Math.sin(player.yaw),fz=-Math.cos(player.yaw);
 for(const m of monsters){if(!m.alive||m.lastSwordSerial===A.attackSerial)continue;const dx=m.root.position.x-player.pos.x,dz=m.root.position.z-player.pos.z,dist=Math.hypot(dx,dz);if(dist>2.35+(m.boss?1.15:.45)*m.cfg.scale||Math.abs(m.root.position.y-player.pos.y)>m.cfg.scale*2.4)continue;if(dist>.1&&(fx*dx+fz*dz)/dist<-.2)continue;m.lastSwordSerial=A.attackSerial;damageMonster(m,A.comboStep===2?103:A.comboStep===1?74:58,'sword');swordHitFx(m,A.comboStep);if(m.alive&&m.anim){m.anim.hitDelay=.2;m.attackCooldown=Math.max(m.attackCooldown,.2);}}
}
// ===================== MONSTER PROCEDURAL ANIMATION =====================
// Grounded gait: every foot is placed by two-bone IK in the monster's own space. Planted feet never leave the floor and
// never slide, because the stride phase is advanced by the distance the monster really moved. Attacks, hit reactions
// (spring-driven flinch + knock-back + stagger) and deaths (buckle / topple, feet planted until the body is down) are
// layered on the same skeleton, so nothing ever lifts a foot off the ground.
const MN_ANKLE=.045;                       // height of a planted ankle above the floor (local units)
const MN_PARAMS={
 brute:  {S:.95,duty:.62,lift:.17,idleHip:1.0, runHip:.98,bob:.04, sway:.075,roll:.05,pYaw:.10,lean:.16,leanRun:.26,arm:.34,elbow:.40,elbowSw:.30,armOut:.17,turn:6,
          atk:{dur:.98,hit:.53,keys:[
           [0,   0,0,0,0,0,      0,0,.15,.3,      0,0,.15,.3],
           [.46,-.5,0,-.14,.12,-.25, -2.6,0,.45,-.6, -2.6,0,.45,-.6],
           [.56, .7,0,.34,.24,.40,   -.9,0,.25,-.2,  -.9,0,.25,-.2],
           [.70, .62,0,.30,.22,.35,  -.8,0,.25,-.25, -.8,0,.25,-.25],
           [.98, 0,0,0,0,0,      0,0,.15,.3,      0,0,.15,.3]]}},
 stalker:{S:1.4,duty:.46,lift:.30,idleHip:.90, runHip:.86,bob:.05, sway:.045,roll:.06,pYaw:.18,lean:.30,leanRun:.50,arm:1.0,elbow:.85,elbowSw:.55,armOut:.10,turn:14,
          atk:{dur:.56,hit:.22,keys:[
           [0,   0,0,0,0,0,      0,0,.10,.5,      0,0,.10,.5],
           [.14, .10,.55,-.06,.05,-.10, -1.15,0,1.35,-1.0,  -.5,0,-.4,-1.0],
           [.23, .38,-.60,.28,.08,.25,  -1.55,0,-.75,-.35,  -.6,0,-.3,-1.0],
           [.33, .35,-.55,.26,.07,.20,  -1.40,0,-.60,-.40,  -.6,0,-.3,-1.0],
           [.56, 0,0,0,0,0,      0,0,.10,.5,      0,0,.10,.5]]}},
 spitter:{S:.9,duty:.6,lift:.20,idleHip:.97, runHip:.95,bob:.035,sway:.06,roll:.05,pYaw:.12,lean:.14,leanRun:.22,arm:.30,elbow:.50,elbowSw:.30,armOut:.20,turn:9,
          atk:{dur:.72,hit:.40,keys:[
           [0,   0,0,0,0,0,      0,0,.20,.5,      0,0,.20,.5],
           [.34,-.4,0,-.08,.06,-.55, -.7,0,.30,-1.3, -.7,0,.30,-1.3],
           [.42, .5,0,.20,.10,.65,   -1.2,0,.35,-.3, -1.2,0,.35,-.3],
           [.55, .45,0,.17,.08,.50,  -1.0,0,.30,-.4, -1.0,0,.30,-.4],
           [.72, 0,0,0,0,0,      0,0,.20,.5,      0,0,.20,.5]]}}
};
const MN_X=new THREE.Vector3(1,0,0),MN_Y=new THREE.Vector3(0,1,0),MN_Z=new THREE.Vector3(0,0,1),MN_DOWN=new THREE.Vector3(0,-1,0);
const _mnQ1=new THREE.Quaternion(),_mnQh=new THREE.Quaternion(),_mnQf=new THREE.Quaternion(),_mnQc=new THREE.Quaternion();
const _mnV=new THREE.Vector3(),_mnD=new THREE.Vector3(),_mnPole=new THREE.Vector3(),_mnK=new THREE.Vector3(),_mnS=new THREE.Vector3(),_mnT=new THREE.Vector3();
function mnClamp(v,a,b){return v<a?a:v>b?b:v;}
function mnSmooth(t){t=mnClamp(t,0,1);return t*t*(3-2*t);}
function mnLerp(a,b,t){return a+(b-a)*t;}
function mnDamp(c,t,k,dt){return t+(c-t)*Math.exp(-k*dt);}
function mnWrap(a){a%=Math.PI*2;if(a>Math.PI)a-=Math.PI*2;else if(a<-Math.PI)a+=Math.PI*2;return a;}
// yaw(Y) · pitch(X) · roll(Z)
function mnSetRot(q,x,y,z){q.setFromAxisAngle(MN_Y,y);_mnQ1.setFromAxisAngle(MN_X,x);q.multiply(_mnQ1);_mnQ1.setFromAxisAngle(MN_Z,z);q.multiply(_mnQ1);return q;}
function mnNewPose(){return{h:[0,1,0,0,0,0],s:[0,0,0,0,0,0,0,0,0],n:[0,0,0],hd:[0,0,0],a:[[0,0,0,0,0],[0,0,0,0,0]],f:[[0,0,0,0,0],[0,0,0,0,0]]};}
function mnBlend(o,a,b,w){for(const k in o){const O=o[k],X=a[k],Y=b[k];for(let i=0;i<O.length;i++){if(typeof O[i]==='number')O[i]=X[i]+(Y[i]-X[i])*w;else for(let j=0;j<O[i].length;j++)O[i][j]=X[i][j]+(Y[i][j]-X[i][j])*w;}}return o;}
function mnCopy(o,a){return mnBlend(o,a,a,0);}

// Two-bone leg IK. T = wanted ankle position in monster space. relW blends toward a hips-local "relaxed" ankle (dead / limp legs).
function mnSolveLeg(m,l,T,pitch,relW,rel){
 const hips=m.rig,a=l.a,b=l.b;
 _mnV.copy(T);
 if(relW>0){   // blend toward the relaxed (limp) ankle, but never let it sink into the floor
  _mnK.set(rel[0],rel[1],rel[2]).applyQuaternion(hips.quaternion).add(hips.position);
  _mnV.x+=(_mnK.x-_mnV.x)*relW;_mnV.y+=(_mnK.y-_mnV.y)*relW;_mnV.z+=(_mnK.z-_mnV.z)*relW;
  if(_mnV.y<m.ankle)_mnV.y=m.ankle;
 }
 _mnQh.copy(hips.quaternion).invert();
 _mnV.sub(hips.position).applyQuaternion(_mnQh).sub(l.upper.position);
 let d=Math.max(_mnV.length(),1e-5);
 const maxD=(a+b)*.999,minD=Math.abs(a-b)+.05;
 if(d>maxD){_mnV.multiplyScalar(maxD/d);d=maxD;}else if(d<minD){_mnV.multiplyScalar(minD/d);d=minD;}
 _mnD.copy(_mnV).multiplyScalar(1/d);
 const cosA=mnClamp((a*a+d*d-b*b)/(2*a*d),-1,1),sinA=Math.sqrt(1-cosA*cosA);
 _mnPole.set(l.side*.1,relW,1-relW).applyQuaternion(_mnQh);   // knee points forward, or up once the legs go limp on the ground
 _mnPole.addScaledVector(_mnD,-_mnPole.dot(_mnD));
 if(_mnPole.lengthSq()<1e-6)_mnPole.set(0,0,1);
 _mnPole.normalize();
 _mnK.copy(_mnD).multiplyScalar(cosA).addScaledVector(_mnPole,sinA);          // thigh direction (unit)
 l.upper.quaternion.setFromUnitVectors(l.upRest,_mnK);
 _mnS.copy(_mnV).addScaledVector(_mnK,-a).normalize();                          // shin direction in hips space
 _mnS.applyQuaternion(_mnQc.copy(l.upper.quaternion).invert());
 l.lower.quaternion.setFromUnitVectors(l.restDir,_mnS);
 _mnQf.copy(hips.quaternion).multiply(l.upper.quaternion).multiply(l.lower.quaternion).invert();   // keep the foot flat to the floor
 mnSetRot(_mnQc,pitch,0,0);
 l.foot.quaternion.copy(_mnQf).multiply(_mnQc);
}
function mnApplyPose(m,P){
 const hp=m.rig,B=m.bone,h=P.h,s=P.s;
 hp.position.set(h[0],h[1],h[2]);mnSetRot(hp.quaternion,h[3],h[4],h[5]);
 mnSetRot(B.spine.quaternion,s[0],s[1],s[2]);mnSetRot(B.spine1.quaternion,s[3],s[4],s[5]);mnSetRot(B.spine2.quaternion,s[6],s[7],s[8]);
 mnSetRot(B.neck.quaternion,P.n[0],P.n[1],P.n[2]);mnSetRot(B.head.quaternion,P.hd[0],P.hd[1],P.hd[2]);
 for(const ar of m.arms){const q=P.a[ar.side<0?0:1];mnSetRot(ar.upper.quaternion,q[0],q[1],q[2]);mnSetRot(ar.fore.quaternion,q[3],0,0);mnSetRot(ar.hand.quaternion,q[4],0,0);}
 for(const l of m.legs){const i=l.side<0?0:1,f=P.f[i];_mnT.set(f[0],f[1],f[2]);mnSolveLeg(m,l,_mnT,f[3],f[4],m.anim.rel[i]);}
 if(m.mx)mnSyncSkeleton(m);
}
// Foot trajectory along the travel axis. Stance: foot slides back at body speed (planted). Swing: Hermite arc whose end
// tangents match the stance speed, so the foot never snaps when it leaves or meets the floor.
function mnGait(P,p,out){
 const S=P.S,d=P.duty;
 if(p<d){const u=p/d;out[0]=S*.5*(1-2*u);out[1]=0;out[2]=mnLerp(-.2,.22,mnSmooth(u));}
 else{
  const u=(p-d)/(1-d),u2=u*u,u3=u2*u,m0=-Math.min(S/d*(1-d),S*.8);
  out[0]=(2*u3-3*u2+1)*(-S*.5)+(u3-2*u2+u)*m0+(-2*u3+3*u2)*(S*.5)+(u3-u2)*m0;
  out[1]=P.lift*Math.pow(Math.sin(Math.PI*u),1.5);out[2]=mnLerp(.22,-.2,mnSmooth(u));
 }
}
function mnSampleKeys(keys,t,out){
 let i=0;while(i<keys.length-2&&t>keys[i+1][0])i++;
 const a=keys[i],b=keys[i+1],u=mnSmooth((t-a[0])/(b[0]-a[0]));
 for(let k=1;k<a.length;k++)out[k-1]=a[k]+(b[k]-a[k])*u;
 return out;
}
const _mnAtk=new Array(13).fill(0),_mnG=[0,0,0];

function mnInit(m){
 const A=m.anim=m.anim||{};
 for(const l of m.legs){l.a=l.lower.position.length();l.b=l.foot.position.length();l.restDir=l.foot.position.clone().normalize();l.upRest=l.lower.position.clone().normalize();}
 m.legReach=m.legs[0].a+m.legs[0].b;
 m.legS=[m.legs.find(l=>l.side<0),m.legs.find(l=>l.side>0)];m.hipW=Math.abs(m.legS[0].upper.position.x);
 if(m.ankle===undefined)m.ankle=MN_ANKLE;                    // planted ankle height of this body
 if(m.lieY===undefined)m.lieY=.4;                            // hip height when lying on the ground
 m.hipOff=(m.ankle-MN_ANKLE)-m.legS[0].upper.position.y;     // converts "hip joint height" tuning values into hips-origin height
 Object.assign(A,{t:Math.random()*20,phase:Math.random(),moveW:0,speed:0,dirX:0,dirZ:1,yaw:0,ready:false,lastX:m.root.position.x,lastZ:m.root.position.z,
  attackT:-1,struck:true,attackSide:1,stance:0,fp:0,fpv:0,fr:0,frv:0,fh:0,fhv:0,stun:0,knockX:0,knockZ:0,deathT:0,deathType:'back',zN:[0,0],
  foot:[new THREE.Vector3(),new THREE.Vector3()],pose:mnNewPose(),deathFrom:mnNewPose(),tmp:mnNewPose(),rel:[[0,0,0],[0,0,0]]});
 m.root.rotation.set(0,0,0);
 mnAnimate(m,.0001);
}

// ---- alive: locomotion + attack + flinch ------------------------------------------------------------------------
function mnAnimate(m,dt){
 const A=m.anim,P=MN_PARAMS[m.type],sc=m.cfg.scale,pose=A.pose,t=A.t+=dt;
 // Real travelled distance (monster space) drives the gait.
 const wx=m.root.position.x-A.lastX,wz=m.root.position.z-A.lastZ;A.lastX=m.root.position.x;A.lastZ=m.root.position.z;
 const cy=Math.cos(A.yaw),sy=Math.sin(A.yaw),lx=(wx*cy-wz*sy)/sc,lz=(wx*sy+wz*cy)/sc,ds=Math.hypot(lx,lz);
 A.speed=mnDamp(A.speed,dt>1e-5?ds/dt:0,14,dt);
 if(ds>1e-4){A.dirX=mnDamp(A.dirX,lx/ds,16,dt);A.dirZ=mnDamp(A.dirZ,lz/ds,16,dt);const n=Math.hypot(A.dirX,A.dirZ)||1;A.dirX/=n;A.dirZ/=n;}
 const mw=A.moveW=mnDamp(A.moveW,mnClamp(A.speed/.8,0,1),12,dt);
 A.phase=(A.phase+ds*P.duty/P.S)%1;
 const ph=A.phase,S=P.S,sw=Math.sin(Math.PI*2*ph),cw=Math.cos(Math.PI*2*ph);
 // flinch springs
 const sp=(x,v,k,c)=>{v+=(-k*x-c*v)*dt;return[x+v*dt,v];};
 let r=sp(A.fp,A.fpv,150,15);A.fp=mnClamp(r[0],-1,.6);A.fpv=r[1];
 r=sp(A.fr,A.frv,120,12);A.fr=r[0];A.frv=r[1];
 r=sp(A.fh,A.fhv,90,9);A.fh=r[0];A.fhv=r[1];
 // attack envelope + keyframes
 let wA=0,atk=null;
 if(A.attackT>=0){
  atk=mnSampleKeys(P.atk.keys,Math.min(A.attackT,P.atk.dur),_mnAtk);
  wA=Math.min(mnSmooth(A.attackT/.08),mnSmooth((P.atk.dur-A.attackT)/.18));
 }
 A.stance=mnDamp(A.stance,A.attackT>=0?1:0,A.attackT>=0?16:7,dt);
 const st=A.stance;
 // feet
 for(let i=0;i<2;i++){
  const s=i===0?-1:1,pp=(ph+(i===0?0:.5))%1;mnGait(P,pp,_mnG);
  A.zN[i]=_mnG[0]/(S*.5);
  let fx=mnLerp(s*(m.hipW+.045),s*(m.hipW+.04)+A.dirX*_mnG[0],mw),fy=mnLerp(m.ankle,m.ankle+_mnG[1],mw),fz=mnLerp(s<0?-.03:.07,A.dirZ*_mnG[0],mw),fp=mnLerp(0,_mnG[2],mw);
  if(st>.001){
   const lead=A.attackSide===s,spit=m.type==='spitter';
   fx=mnLerp(fx,s*(m.hipW+(m.type==='brute'?.115:.075)),st);fy=mnLerp(fy,m.ankle,st);fz=mnLerp(fz,spit?(lead?.07:-.03):(lead?.24:-.2),st);fp=mnLerp(fp,0,st);
  }
  A.foot[i].set(fx,fy,fz);A.zN[i+2]=fp;
 }
 // pelvis
 const lunge=atk?wA*atk[2]:0,drop=atk?wA*atk[3]:0;
 const hx=-P.sway*sw*mw,hz=lunge;
 let hy=mnLerp(P.idleHip+.01*Math.sin(t*1.7),P.runHip,mw)+P.bob*mw*(.5-.5*Math.cos(Math.PI*4*ph))+m.hipOff;
 const R=.985*m.legReach;
 for(let i=0;i<2;i++){const T=A.foot[i],up=m.legS[i].upper.position,hh=Math.hypot(T.x-(hx+up.x),T.z-(hz+up.z));hy=Math.min(hy,T.y+Math.sqrt(Math.max(0,R*R-hh*hh))-up.y);}
 hy=Math.max(hy,.5+m.hipOff)-drop-.08*Math.min(1,Math.abs(A.fp));
 pose.h[0]=hx;pose.h[1]=hy;pose.h[2]=hz;pose.h[3]=A.fp*.25;pose.h[4]=P.pYaw*cw*mw;pose.h[5]=-P.roll*sw*mw;
 // spine / head
 const lean=mnLerp(P.lean,P.leanRun,mw)+(atk?wA*atk[0]:0)+A.fp*.95+.015*Math.sin(t*1.7);
 const side=A.attackSide;
 const twist=-1.3*P.pYaw*cw*mw+(atk?wA*atk[1]*side:0)+A.frv*.01;
 const roll=P.roll*sw*mw*.9+A.fr*.5;
 for(let k=0;k<3;k++){pose.s[k*3]=lean*(k?.33:.34);pose.s[k*3+1]=twist/3;pose.s[k*3+2]=roll/3;}
 pose.n[0]=-lean*.15;pose.n[1]=0;pose.n[2]=-roll*.2;
 pose.hd[0]=-lean*.65+(atk?wA*atk[4]:0)+A.fh;pose.hd[1]=.12*Math.sin(t*.8)*(1-mw)-twist*.3;pose.hd[2]=A.fr*.3;
 // arms: counter-swing against the opposite leg, then blend into the attack keyframes
 const flare=mnClamp(-A.fp,0,1)*.9;
 for(let i=0;i<2;i++){
  const s=i?1:-1,fN=A.zN[1-i]*A.dirZ,rest=lean*.72-.08;
  let ux=rest-P.arm*fN*mw+.05*Math.sin(t*1.3+i*2)*(1-mw),uy=0,uz=s*(P.armOut+flare),fx=-(.25*(1-mw)+P.elbow*.6*mw+P.elbowSw*mnClamp(fN,0,1)*mw),hxr=-.25;
  if(atk){
   const lead=m.type!=='stalker'||s===side,o=lead?5:9;
   ux=mnLerp(ux,atk[o],wA);uy=mnLerp(uy,atk[o+1]*s,wA);uz=mnLerp(uz,atk[o+2]*s,wA);fx=mnLerp(fx,atk[o+3],wA);hxr=mnLerp(hxr,-.55,wA);
  }
  const q=pose.a[i];q[0]=ux;q[1]=uy;q[2]=uz;q[3]=fx;q[4]=hxr;
 }
 for(let i=0;i<2;i++){const f=pose.f[i],T=A.foot[i];f[0]=T.x;f[1]=T.y;f[2]=T.z;f[3]=A.zN[i+2];f[4]=0;}
 mnApplyPose(m,pose);
}

// ---- dying --------------------------------------------------------------------------------------------------------
function mnBeginDeath(m){
 const A=m.anim;mnCopy(A.deathFrom,A.pose);
 A.deathT=0;A.attackT=-1;A.deathType=m.type==='brute'?'kneel':'back';
 for(let i=0;i<2;i++){const s=i?1:-1;A.rel[i][0]=s*(m.hipW+.075);A.rel[i][1]=-.89*m.legReach;A.rel[i][2]=-.04;}
 m.deadTimer=A.deathType==='kneel'?3.7:3.1;
}
function mnBeginDeathLying(m){   // killed while knocked down: no stand-up + death animation, the body stays exactly as it lies
 const A=m.anim,d=m.down;
 if(!d.init){d.init=true;mnCopy(A.deathFrom,A.pose);A.deathType='back';for(let i=0;i<2;i++){const s=i?1:-1;A.rel[i][0]=s*(m.hipW+.075);A.rel[i][1]=-.89*m.legReach;A.rel[i][2]=-.04;}}
 A.deathT=0;A.attackT=-1;
 m.lieAir=!!d.air;m.lieTT=d.air?(d.tt||0):(d.cur!==undefined?d.cur:.85);m.deadTimer=3.1;m.down=null;
}
function mnDeathPose(m,tt,out){
 const A=m.anim,f=A.deathFrom,PI=Math.PI;
 mnCopy(out,f);
 const back=A.deathType==='back',decay=Math.exp(-3.2*tt),lie=PI/2-.04;
 let hy,hz,pitch,spineP,headP,landT;
 if(back){
  const T1=.85,u=mnClamp(tt/T1,0,1);
  pitch=mnLerp(f.h[3],-lie,u*u);hy=mnLerp(f.h[1],m.lieY,u*u);hz=mnLerp(f.h[2],-.5,mnSmooth(u));
  spineP=mnLerp(f.s[0],-.05,mnSmooth(u));headP=mnLerp(f.hd[0],-.3,mnSmooth((tt-.2)/.5));landT=tt-T1;
 }else{
  const k=mnSmooth(tt/.55),u=mnClamp((tt-.55)/.9,0,1);
  pitch=mnLerp(mnLerp(f.h[3],.1,k),lie,u*u);hy=mnLerp(mnLerp(f.h[1],.52,k),m.lieY,u*u);hz=mnLerp(mnLerp(f.h[2],f.h[2]+.12,k),.5,mnSmooth(u));
  spineP=mnLerp(mnLerp(f.s[0],.12,k),.04,mnSmooth(u));headP=mnLerp(mnLerp(f.hd[0],.3,k),.1,mnSmooth(u));landT=tt-1.45;
 }
 if(landT>0)hy+=.05*Math.exp(-9*landT)*Math.abs(Math.sin(18*landT));
 const w0=mnSmooth(tt/.4);
 out.h[1]=hy;out.h[2]=hz;out.h[3]=pitch;out.h[4]=mnLerp(f.h[4],0,w0);out.h[5]=mnLerp(f.h[5],0,w0);out.h[0]=mnLerp(f.h[0],0,w0);
 for(let k=0;k<3;k++){out.s[k*3]=spineP;out.s[k*3+1]=mnLerp(f.s[k*3+1],0,w0);out.s[k*3+2]=mnLerp(f.s[k*3+2],0,w0);}
 out.hd[0]=headP;out.hd[2]=mnLerp(f.hd[2],.35,mnSmooth(tt/.6));out.hd[1]=mnLerp(f.hd[1],0,w0);
 const wa=mnSmooth(tt/.2);
 for(let i=0;i<2;i++){
  const s=i?1:-1,q=out.a[i],g=f.a[i];
  const ux=back?.1-.9*decay*Math.cos(7*tt):.2+.25*(1-decay)+.2*decay*Math.cos(6*tt),uz=s*(.55+.8*decay),fx=-(.3+.5*decay);
  q[0]=mnLerp(g[0],ux,wa);q[2]=mnLerp(g[2],uz,wa);q[3]=mnLerp(g[3],fx,wa);q[1]=mnLerp(g[1],0,wa);q[4]=mnLerp(g[4],-.3,wa);
  out.f[i][4]=mnSmooth((tt-(back?.15:.8))/.6);
 }
}
function mnAnimateDeath(m,dt){
 const A=m.anim;A.deathT+=dt;
 mnDeathPose(m,m.lieTT===undefined?A.deathT:(m.lieAir?Math.min(.85,m.lieTT+A.deathT*1.2):m.lieTT),A.tmp);mnApplyPose(m,A.tmp);
 m.deathVy=(m.deathVy||0)+26*dt;m.deathY0=Math.max(0,(m.deathY0||0)-m.deathVy*dt);m.root.position.y=m.spawn.y+m.deathY0-(m.deadTimer<.8?(1-m.deadTimer/.8)*.9:0);   // corpses fall off roofs   // finally sink into the street
}

// ===================== RAGDOLL PHYSICS: monsters die as limp bodies instead of a scripted fall =====================
// Every dying monster becomes a Verlet ragdoll: 20 joint points (hips, belly, chest, neck, head, shoulders, elbows, wrists, hips joints,
// knees, ankles, toes) held together by bone-length constraints, a soft torso, and limits that stop knees / elbows / the head from bending
// the wrong way. The killing blow throws the body (heavy monsters fly less), it keeps the speed it had while running, collides with the
// street, buildings, props and roofs, tumbles and finally lies still. The simulation is written back onto the same proxy skeleton the
// animation uses, so it works for the skinned FBX bodies (through mnSyncSkeleton) and for the procedural fallback bodies alike.
// Tweak live from the console, e.g.  RAGDOLL.gravity=12   RAGDOLL.push.sword=14   RAGDOLL.life=10   RAGDOLL.enabled=false  (old scripted death)
const RAGDOLL={enabled:true,gravity:19,damping:.994,friction:.5,bounce:.1,iters:3,life:4.5,sink:1.2,sleepAfter:.35,settleMax:2.5,maxSteps:2,
 push:{sword:7.5,arrow:5.5,kick:12,other:6.5},lift:2.4,twist:.45,range:10,step:.7,maxSpeed:22,weight:{brute:.7,stalker:1.15,spitter:.95}};
const RD_N=20,RD_HIP=0,RD_BEL=1,RD_CHE=2,RD_NEC=3,RD_HED=4,RD_TIP=5,RD_SHL=6,RD_SHR=7,RD_ELL=8,RD_ELR=9,RD_WRL=10,RD_WRR=11,RD_HJL=12,RD_HJR=13,RD_KNL=14,RD_KNR=15,RD_ANL=16,RD_ANR=17,RD_TOL=18,RD_TOR=19;
const RD_RAD=[.14,.14,.17,.07,.14,.07,.10,.10,.07,.07,.06,.06,.11,.11,.09,.09,.05,.05,.02,.02];   // collision radius of every joint point (monster-local units)
const RD_INV=[.6,.6,.5,1,1,1.5,.9,.9,1.4,1.4,2,2,.8,.8,1.1,1.1,1.5,1.5,2,2];                       // inverse mass: the trunk is heavy, hands and feet are light
const RD_CON=[   // [a,b,stiffness]  equal-distance constraints, lengths are measured from the pose the monster dies in
 [0,1,1],[1,2,1],[2,3,1],[3,4,1],[4,5,1],                          // spine, neck, head
 [2,6,1],[2,7,1],[3,6,1],[3,7,1],[6,7,1],                          // shoulder girdle
 [6,8,1],[8,10,1],[7,9,1],[9,11,1],                                // arms
 [0,12,1],[0,13,1],[12,13,1],[1,12,1],[1,13,1],                    // pelvis
 [12,14,1],[14,16,1],[13,15,1],[15,17,1],                          // legs
 [16,18,1],[17,19,1],[14,18,.8],[15,19,.8],                        // feet
 [0,2,.5],[1,3,.5],[6,12,.6],[7,13,.6],[6,13,.5],[7,12,.5],[2,12,.6],[2,13,.6]   // soft torso: lets the body bend and twist a little
];
const RD_LIM=[   // [a,b,chain,factor]  minimum distance = factor * chain length  (knees / elbows can fold, but not through themselves; head can't fold into the chest)
 [12,16,[[12,14],[14,16]],.35],[13,17,[[13,15],[15,17]],.35],[6,10,[[6,8],[8,10]],.3],[7,11,[[7,9],[9,11]],.3],[2,5,[[2,3],[3,4],[4,5]],.8],[0,3,[[0,1],[1,2],[2,3]],.8]
];
const _rdA=new THREE.Vector3(),_rdB=new THREE.Vector3(),_rdC=new THREE.Vector3(),_rdX=new THREE.Vector3(),_rdY=new THREE.Vector3(),_rdZ=new THREE.Vector3();
const _rdM=new THREE.Matrix4(),_rdQ=new THREE.Quaternion();
// position + orientation of a proxy joint in root-local space, from the current local transforms (the proxy rig is axis-aligned at rest)
function rdFK(m,obj,p,q){
 const top=m.rig.parent,chain=[];for(let o=obj;o&&o!==top;o=o.parent)chain.push(o);
 p.set(0,0,0);q.identity();
 for(let i=chain.length-1;i>=0;i--){const o=chain[i];_rdC.copy(o.position).applyQuaternion(q);p.add(_rdC);q.multiply(o.quaternion);}
}
function rdRestPos(m,obj,out){const top=m.rig.parent;out.set(0,0,0);for(let o=obj;o&&o!==top;o=o.parent)out.add(o.position);return out;}
// orthonormal frame (x = lat, y = up made perpendicular to it) -> quaternion
function rdBasis(out,lat,up){
 _rdX.copy(lat);if(_rdX.lengthSq()<1e-10)_rdX.set(1,0,0);_rdX.normalize();
 _rdY.copy(up);_rdY.addScaledVector(_rdX,-_rdY.dot(_rdX));
 if(_rdY.lengthSq()<1e-10){_rdY.set(0,1,0);_rdY.addScaledVector(_rdX,-_rdX.y);if(_rdY.lengthSq()<1e-10)_rdY.set(0,0,1);}
 _rdY.normalize();_rdZ.crossVectors(_rdX,_rdY);
 _rdM.makeBasis(_rdX,_rdY,_rdZ);return out.setFromRotationMatrix(_rdM);
}
function rdGather(rd,cx,cz){   // solid boxes close to the body (buildings, roofs, props ...): [minx,maxx,minz,maxz,bottom,top]
 const out=[],R=RAGDOLL.range*rd.sc/1.5+RAGDOLL.range*.4;
 for(const c of colliders){
  if(c.top<.3)continue;
  const dx=Math.max(c.x-c.halfX-cx,0,cx-(c.x+c.halfX)),dz=Math.max(c.z-c.halfZ-cz,0,cz-(c.z+c.halfZ));
  if(dx*dx+dz*dz>R*R)continue;
  out.push(c.x-c.halfX,c.x+c.halfX,c.z-c.halfZ,c.z+c.halfZ,c.bottom||0,c.top);
 }
 rd.cols=new Float32Array(out);rd.nc=out.length/6;rd.colX=cx;rd.colZ=cz;
}
function mnRagdollStart(m,kind,amount){
 if(!RAGDOLL.enabled)return false;
 const B=m.bone,ar=m.arms,lg=m.legs;
 if(!B||!ar||!lg||ar.length<2||lg.length<2||!m.rig||!m.rig.parent||!B.spine||!B.spine1||!B.spine2||!B.neck||!B.head)return false;
 try{
  const sc=m.cfg.scale,A=m.anim||{};m.root.updateMatrixWorld(true);
  const rd={p:new Float32Array(RD_N*3),q:new Float32Array(RD_N*3),vy:new Float32Array(RD_N),r:new Float32Array(RD_N),w:new Float32Array(RD_INV),flag:new Uint8Array(RD_N),
   sc,h:1/60,acc:0,t:0,calm:0,asleep:false,sink:0,gy:m.spawn.y-.035,lim:WORLD.wallRadius-2,fsgn:1,cols:null,nc:0,colX:0,colZ:0,calmEps:.004*sc,
   L:[],hipsRestInv:new THREE.Quaternion(),s2RestInv:new THREE.Quaternion(),toeDir:[new THREE.Vector3(),new THREE.Vector3()],
   v1:new THREE.Vector3(),v2:new THREE.Vector3(),Qh:new THREE.Quaternion(),Qs1:new THREE.Quaternion(),Qs2:new THREE.Quaternion(),Qn:new THREE.Quaternion(),Qhd:new THREE.Quaternion(),
   Qa:new THREE.Quaternion(),Qb:new THREE.Quaternion(),Qc:new THREE.Quaternion()};
  for(let i=0;i<RD_N;i++){rd.L.push(new THREE.Vector3());rd.r[i]=RD_RAD[i]*sc;}
  const ank=Math.max(m.ankle||.045,.05);rd.r[RD_ANL]=rd.r[RD_ANR]=ank*sc;
  // rest-pose frames (all proxy joints are identity-rotated at rest)
  const restLat=_rdA.subVectors(lg[1].upper.position,lg[0].upper.position).clone(),restUp=_rdB.copy(B.spine.position).add(B.spine1.position).clone();
  rd.fsgn=_rdC.crossVectors(restLat,restUp).z>=0?1:-1;
  rdBasis(rd.hipsRestInv,restLat,restUp).invert();
  const rl2=rdRestPos(m,ar[1].upper,new THREE.Vector3()).sub(rdRestPos(m,ar[0].upper,new THREE.Vector3()));
  rdBasis(rd.s2RestInv,rl2,B.neck.position).invert();
  // joint points from the pose the monster dies in
  const objs=[m.rig,B.spine1,B.spine2,B.neck,B.head,null,ar[0].upper,ar[1].upper,ar[0].fore,ar[1].fore,ar[0].hand,ar[1].hand,lg[0].upper,lg[1].upper,lg[0].lower,lg[1].lower,lg[0].foot,lg[1].foot,null,null];
  const pl=[],ql=[];for(let i=0;i<RD_N;i++){pl.push(new THREE.Vector3());ql.push(new THREE.Quaternion());}
  for(let i=0;i<RD_N;i++)if(objs[i])rdFK(m,objs[i],pl[i],ql[i]);
  const headLen=Math.min(.32,Math.max(.16,1.8*B.head.position.length()));
  pl[RD_TIP].set(0,headLen,0).applyQuaternion(ql[RD_HED]).add(pl[RD_HED]);
  for(let k=0;k<2;k++){
   rd.toeDir[k].set(0,-ank*.8,.17);const toe=rd.toeDir[k].clone().applyQuaternion(ql[RD_ANL+k]).add(pl[RD_ANL+k]);pl[RD_TOL+k].copy(toe);rd.toeDir[k].normalize();
  }
  const P=rd.p;
  for(let i=0;i<RD_N;i++){_rdA.copy(pl[i]).applyMatrix4(m.root.matrixWorld);P[i*3]=_rdA.x;P[i*3+1]=_rdA.y;P[i*3+2]=_rdA.z;}
  // constraints with measured lengths
  const dist=(a,b)=>Math.hypot(P[a*3]-P[b*3],P[a*3+1]-P[b*3+1],P[a*3+2]-P[b*3+2]);
  const nC=RD_CON.length+RD_LIM.length;rd.cn=nC;rd.ca=new Uint8Array(nC);rd.cb=new Uint8Array(nC);rd.cl=new Float32Array(nC);rd.ck=new Float32Array(nC);rd.ct=new Uint8Array(nC);
  let n=0;
  for(const [a,b,k] of RD_CON){rd.ca[n]=a;rd.cb[n]=b;rd.cl[n]=dist(a,b);rd.ck[n]=k;rd.ct[n]=0;n++;}
  for(const [a,b,chain,f] of RD_LIM){let s=0;for(const [x,y] of chain)s+=dist(x,y);rd.ca[n]=a;rd.cb[n]=b;rd.cl[n]=s*f;rd.ck[n]=.6;rd.ct[n]=1;n++;}
  // initial velocity: what the monster was doing + the force of the killing blow
  let vx=0,vy=0,vz=0;
  const speed=Math.min(9,Math.max(0,A.speed||0))*sc,yaw=A.yaw||m.root.rotation.y||0;
  if(!m.entry&&!m.down){vx=Math.sin(yaw)*speed;vz=Math.cos(yaw)*speed;}
  if(m.down&&m.down.air)vy=m.down.vy||0;
  let dx=m.root.position.x-player.pos.x,dz=m.root.position.z-player.pos.z,dl=Math.hypot(dx,dz);
  if(dl<.2){dx=-Math.sin(yaw);dz=-Math.cos(yaw);dl=1;}dx/=dl;dz/=dl;
  const push=(RAGDOLL.push[kind]!==undefined?RAGDOLL.push[kind]:RAGDOLL.push.other)*(RAGDOLL.weight[m.type]||1)*(amount>9000?1.25:1);
  const yh=P[1],ref=Math.max(.5,P[RD_HED*3+1]-yh),side=Math.random()<.5?-1:1;
  for(let i=0;i<RD_N;i++){
   const o=i*3,hw=Math.max(-.6,Math.min(1,(P[o+1]-yh)/ref)),kp=hw>0?.6+.7*hw:.6+.35*hw;
   let ux=vx+dx*push*kp-dz*side*push*RAGDOLL.twist*Math.max(0,hw)+(Math.random()-.5)*push*.18;
   let uy=vy+RAGDOLL.lift*(.5+.5*Math.max(0,hw))*(kind==='kick'?1.6:1)+(Math.random()-.5)*.8;
   let uz=vz+dz*push*kp+dx*side*push*RAGDOLL.twist*Math.max(0,hw)+(Math.random()-.5)*push*.18;
   const sp=Math.hypot(ux,uy,uz);if(sp>RAGDOLL.maxSpeed){const k=RAGDOLL.maxSpeed/sp;ux*=k;uy*=k;uz*=k;}
   rd.q[o]=P[o]-ux*rd.h;rd.q[o+1]=P[o+1]-uy*rd.h;rd.q[o+2]=P[o+2]-uz*rd.h;
  }
  rdGather(rd,P[0],P[2]);
  m.down=null;m.deadTimer=RAGDOLL.life;m.rd=rd;
  return true;
 }catch(err){console.warn('Ragdoll failed, using the scripted death instead:',err);m.rd=null;return false;}
}
function rdSolve(rd){
 const P=rd.p,W=rd.w,A=rd.ca,Bn=rd.cb,Lm=rd.cl,K=rd.ck,T=rd.ct,n=rd.cn;
 for(let c=0;c<n;c++){
  const ia=A[c],ib=Bn[c],a=ia*3,b=ib*3,dx=P[b]-P[a],dy=P[b+1]-P[a+1],dz=P[b+2]-P[a+2],d2=dx*dx+dy*dy+dz*dz;
  if(d2<1e-12)continue;
  const d=Math.sqrt(d2),len=Lm[c];
  if(T[c]===1&&d>=len)continue;
  const wa=W[ia],wb=W[ib],f=(d-len)/(d*(wa+wb))*K[c];
  P[a]+=dx*f*wa;P[a+1]+=dy*f*wa;P[a+2]+=dz*f*wa;P[b]-=dx*f*wb;P[b+1]-=dy*f*wb;P[b+2]-=dz*f*wb;
 }
}
// knees bend forward, elbows backward: if the middle joint lies on the wrong side of the line between its neighbours, push it back across
function rdPole(P,a,b,c,fx,fy,fz,sgn,k,eps){
 const ao=a*3,bo=b*3,co=c*3,ux=P[co]-P[ao],uy=P[co+1]-P[ao+1],uz=P[co+2]-P[ao+2],L2=ux*ux+uy*uy+uz*uz;if(L2<1e-8)return;
 const bx=P[bo]-P[ao],by=P[bo+1]-P[ao+1],bz=P[bo+2]-P[ao+2],t=(bx*ux+by*uy+bz*uz)/L2,ox=bx-ux*t,oy=by-uy*t,oz=bz-uz*t;
 if((ox*fx+oy*fy+oz*fz)*sgn<-eps){P[bo]-=ox*2*k;P[bo+1]-=oy*2*k;P[bo+2]-=oz*2*k;}
}
function rdPoles(rd){
 const P=rd.p,lx=P[39]-P[36],ly=P[40]-P[37],lz=P[41]-P[38],ux=P[3]-P[0],uy=P[4]-P[1],uz=P[5]-P[2];
 let fx=(ly*uz-lz*uy)*rd.fsgn,fy=(lz*ux-lx*uz)*rd.fsgn,fz=(lx*uy-ly*ux)*rd.fsgn;const fl=Math.hypot(fx,fy,fz);if(fl<1e-8)return;fx/=fl;fy/=fl;fz/=fl;
 const e=.012*rd.sc;
 rdPole(P,RD_HJL,RD_KNL,RD_ANL,fx,fy,fz,1,.35,e);rdPole(P,RD_HJR,RD_KNR,RD_ANR,fx,fy,fz,1,.35,e);
 rdPole(P,RD_SHL,RD_ELL,RD_WRL,fx,fy,fz,-1,.3,e);rdPole(P,RD_SHR,RD_ELR,RD_WRR,fx,fy,fz,-1,.3,e);
}
// street, arena wall and solid boxes. Landing on something lower than RAGDOLL.step is a step-up (curbs, sloped roofs), anything taller is a wall.
function rdCollide(rd){
 const P=rd.p,R=rd.r,cols=rd.cols,nc=rd.nc,gy=rd.gy,stepH=RAGDOLL.step*rd.sc,F=rd.flag,lim=rd.lim;
 for(let i=0;i<RD_N;i++){
  const o=i*3,r=R[i];let x=P[o],y=P[o+1],z=P[o+2];
  const rr=x*x+z*z;if(rr>lim*lim){const k=lim/Math.sqrt(rr);x*=k;z*=k;F[i]|=6;}
  for(let c=0;c<nc;c++){
   const b=c*6,minx=cols[b]-r,maxx=cols[b+1]+r,minz=cols[b+2]-r,maxz=cols[b+3]+r,bot=cols[b+4]-r,top=cols[b+5]+r;
   if(x<=minx||x>=maxx||z<=minz||z>=maxz||y>=top||y<=bot)continue;
   const du=top-y;
   if(du<=stepH){y=top;F[i]|=1;continue;}
   const dl=x-minx,dr=maxx-x,dn=z-minz,df=maxz-z,mh=Math.min(dl,dr,dn,df);
   if(mh===dl){x=minx;F[i]|=2;}else if(mh===dr){x=maxx;F[i]|=2;}else if(mh===dn){z=minz;F[i]|=4;}else{z=maxz;F[i]|=4;}
  }
  if(y<gy+r){y=gy+r;F[i]|=1;}
  P[o]=x;P[o+1]=y;P[o+2]=z;
 }
}
function rdStep(rd,h){
 const P=rd.p,Q=rd.q,VY=rd.vy,F=rd.flag,gdt=RAGDOLL.gravity*h*h,damp=RAGDOLL.damping;
 for(let i=0,j=0;i<RD_N;i++,j+=3){
  const x=P[j],y=P[j+1],z=P[j+2],vx=(x-Q[j])*damp,vy=(y-Q[j+1])*damp,vz=(z-Q[j+2])*damp;
  Q[j]=x;Q[j+1]=y;Q[j+2]=z;P[j]=x+vx;P[j+1]=y+vy-gdt;P[j+2]=z+vz;VY[i]=vy-gdt;F[i]=0;
 }
 const it=RAGDOLL.iters;
 for(let k=0;k<it;k++){rdSolve(rd);rdPoles(rd);rdCollide(rd);}
 // contact response: ground friction / small bounce, walls kill the velocity into them
 const fr=RAGDOLL.friction,bn=RAGDOLL.bounce;let e=0;
 for(let i=0,j=0;i<RD_N;i++,j+=3){
  const f=F[i];
  if(f&1){Q[j]+=(P[j]-Q[j])*fr;Q[j+2]+=(P[j+2]-Q[j+2])*fr;const vy=VY[i];Q[j+1]=vy<-.04?P[j+1]+bn*vy:P[j+1];}
  if(f&2)Q[j]=P[j];
  if(f&4)Q[j+2]=P[j+2];
  let d=Math.max(Math.abs(P[j]-Q[j]),Math.abs(P[j+1]-Q[j+1]),Math.abs(P[j+2]-Q[j+2]));
  if((f&1)&&d<rd.calmEps*2.5){Q[j]=P[j];Q[j+1]=P[j+1];Q[j+2]=P[j+2];d=0;}   // a joint resting on the ground and barely moving is frozen: no more twitching limbs
  if(d>e)e=d;
 }
 if(e<rd.calmEps)rd.calm+=h;else rd.calm=Math.max(0,rd.calm-h*.5);
 if(rd.calm>RAGDOLL.sleepAfter||rd.t>RAGDOLL.settleMax)rd.asleep=true;   // everything lies still (or the time limit is up): the body is frozen for good
}
// simulation -> proxy skeleton (root-local frame, origin at the hips). Every bone gets the minimal rotation that points it at its child joint.
function rdWrite(m,rd){
 const P=rd.p,sc=rd.sc,th=m.root.rotation.y,cs=Math.cos(th),sn=Math.sin(th),hx=P[0],hy=P[1],hz=P[2],L=rd.L,inv=1/sc;
 for(let i=0,o=0;i<RD_N;i++,o+=3){const dx=P[o]-hx,dy=P[o+1]-hy,dz=P[o+2]-hz;L[i].set((cs*dx-sn*dz)*inv,dy*inv,(sn*dx+cs*dz)*inv);}
 const B=m.bone,ar=m.arms,lg=m.legs,v1=rd.v1,v2=rd.v2,Qh=rd.Qh,Qs1=rd.Qs1,Qs2=rd.Qs2,Qn=rd.Qn,Qhd=rd.Qhd,Qa=rd.Qa,Qb=rd.Qb,Qc=rd.Qc;
 // hips: frame from the hip joints (lateral) and the spine direction (up)
 v1.subVectors(L[RD_HJR],L[RD_HJL]);v2.subVectors(L[RD_BEL],L[RD_HIP]);
 rdBasis(Qh,v1,v2).multiply(rd.hipsRestInv);
 m.rig.position.set(0,0,0);m.rig.quaternion.copy(Qh);B.spine.quaternion.identity();
 // belly bone points at the chest
 v1.copy(B.spine2.position).applyQuaternion(Qh).normalize();v2.subVectors(L[RD_CHE],L[RD_BEL]).normalize();
 Qs1.setFromUnitVectors(v1,v2).multiply(Qh);B.spine1.quaternion.copy(Qh).invert().multiply(Qs1);
 // chest: frame from the shoulders (lateral) and the neck direction (up)
 v1.subVectors(L[RD_SHR],L[RD_SHL]);v2.subVectors(L[RD_NEC],L[RD_CHE]);
 rdBasis(Qs2,v1,v2).multiply(rd.s2RestInv);B.spine2.quaternion.copy(Qs1).invert().multiply(Qs2);
 // neck and head
 v1.copy(B.head.position).applyQuaternion(Qs2).normalize();v2.subVectors(L[RD_HED],L[RD_NEC]).normalize();
 Qn.setFromUnitVectors(v1,v2).multiply(Qs2);B.neck.quaternion.copy(Qs2).invert().multiply(Qn);
 v1.set(0,1,0).applyQuaternion(Qn);v2.subVectors(L[RD_TIP],L[RD_HED]).normalize();
 Qhd.setFromUnitVectors(v1,v2).multiply(Qn);B.head.quaternion.copy(Qn).invert().multiply(Qhd);
 for(let k=0;k<2;k++){
  const a=ar[k],SH=RD_SHL+k,EL=RD_ELL+k,WR=RD_WRL+k;
  v1.copy(a.fore.position).applyQuaternion(Qs2).normalize();v2.subVectors(L[EL],L[SH]).normalize();
  Qa.setFromUnitVectors(v1,v2).multiply(Qs2);a.upper.quaternion.copy(Qs2).invert().multiply(Qa);
  v1.copy(a.hand.position).applyQuaternion(Qa).normalize();v2.subVectors(L[WR],L[EL]).normalize();
  Qb.setFromUnitVectors(v1,v2).multiply(Qa);a.fore.quaternion.copy(Qa).invert().multiply(Qb);a.hand.quaternion.identity();
  const l=lg[k],HJ=RD_HJL+k,KN=RD_KNL+k,AN=RD_ANL+k,TO=RD_TOL+k;
  v1.copy(l.lower.position).applyQuaternion(Qh).normalize();v2.subVectors(L[KN],L[HJ]).normalize();
  Qa.setFromUnitVectors(v1,v2).multiply(Qh);l.upper.quaternion.copy(Qh).invert().multiply(Qa);
  v1.copy(l.foot.position).applyQuaternion(Qa).normalize();v2.subVectors(L[AN],L[KN]).normalize();
  Qb.setFromUnitVectors(v1,v2).multiply(Qa);l.lower.quaternion.copy(Qa).invert().multiply(Qb);
  v1.copy(rd.toeDir[k]).applyQuaternion(Qb);v2.subVectors(L[TO],L[AN]).normalize();
  Qc.setFromUnitVectors(v1,v2).multiply(Qb);l.foot.quaternion.copy(Qb).invert().multiply(Qc);
 }
 if(m.mx)mnSyncSkeleton(m);
}
function mnRagdollStep(m,dt){
 const rd=m.rd;if(!rd)return;
 rd.t+=dt;
 const S=RAGDOLL.sink,sk=m.deadTimer<S?Math.min(1,1-Math.max(0,m.deadTimer)/S):0;rd.sink=sk*sk*(3-2*sk)*1.3*rd.sc;   // slowly sinks into the street before it disappears
 if(!rd.asleep){
  rd.acc+=Math.min(dt,.1);let n=0;
  while(rd.acc>=rd.h&&n<RAGDOLL.maxSteps){rdStep(rd,rd.h);rd.acc-=rd.h;n++;}
  if(rd.acc>=rd.h)rd.acc=0;
  if(rd.cols&&Math.hypot(rd.p[0]-rd.colX,rd.p[2]-rd.colZ)>RAGDOLL.range*.45)rdGather(rd,rd.p[0],rd.p[2]);
  if(n>0)rdWrite(m,rd);
 }
 m.root.position.set(rd.p[0],rd.p[1]-rd.sink,rd.p[2]);
}

// ---- hit reaction -------------------------------------------------------------------------------------------------
function mnHitReact(m,amount,kind){
 const A=m.anim,str=mnClamp(amount/85,.35,1.15)*(kind==='arrow'?.8:1),heavy=m.type==='brute'?.75:m.type==='stalker'?1.15:.95;
 A.fpv-=12*str*heavy;A.frv+=(Math.random()<.5?-1:1)*4*str;A.fhv-=14*str;
 A.stun=Math.max(A.stun,(kind==='arrow'?.14:.3)*heavy*(.7+.4*str));
 if(A.attackT>=0&&!A.struck&&(m.type!=='brute'||str>.8))A.attackT=-1;   // a heavy blow breaks the wind-up
 mnKnock(m,(kind==='arrow'?1.2:3.4)*str/m.cfg.scale);
}
function mnKnock(m,mag){
 const A=m.anim,dx=m.root.position.x-player.pos.x,dz=m.root.position.z-player.pos.z,l=Math.hypot(dx,dz)||1;
 A.knockX+=dx/l*mag;A.knockZ+=dz/l*mag;
}
// ---- retargeting onto a skinned Mixamo-style character ---------------------------------------------------------------
// The animation above runs on a hidden "proxy" skeleton that has the character's real proportions (measured from its rest pose,
// all bones axis-aligned). Every frame the proxy's world rotations are transferred to the real bones as
//   W(bone) = proxyWorldRotation * C * restWorldRotation      (C: rest-arm -> hanging-arm correction, identity elsewhere)
// so joints land exactly where the IK put them and the planted feet stay on the floor, whatever the bone axes are.
// desc: lower-case bone name (no "mixamorig") -> {p:Vector3 rest position, q:Quaternion rest world rotation}; bones: name -> bone object.
const _mnPW=new THREE.Quaternion();
function mnBuildModelRig(m,desc,bones,f){
 const D=n=>{if(!desc[n]||!bones[n])throw new Error('Monster model is missing bone: '+n);return desc[n];};
 const V=(a,b,k)=>D(b).p.clone().sub(D(a).p).multiplyScalar(k===undefined?f:k);
 const mk=pos=>{const g=new THREE.Group();g.position.copy(pos);return g;};
 const proxyRoot=new THREE.Group(),hips=mk(new THREE.Vector3());proxyRoot.add(hips);
 D('hips');const spine=mk(V('hips','spine')),spine1=mk(V('spine','spine1')),spine2=mk(V('spine1','spine2')),neck=mk(V('spine2','neck')),head=mk(V('neck','head'));
 hips.add(spine);spine.add(spine1);spine1.add(spine2);spine2.add(neck);neck.add(head);
 const arms=[],legs=[],list=[];
 const add=(key,proxy,C,parentIdx,parentKey)=>{
  const R=D(key).q.clone();let K=null;
  if(parentIdx>=0&&desc[key].parent!==parentKey)K=D(parentKey).q.clone().invert().multiply(D(desc[key].parent).q);   // undriven bone in between (shoulder)
  list.push({bone:bones[key],proxy,C:C||new THREE.Quaternion(),R,parentIdx,K,dq:new THREE.Quaternion(),W:new THREE.Quaternion()});return list.length-1;};
 const ih=add('hips',hips,null,-1),is=add('spine',spine,null,ih,'hips'),is1=add('spine1',spine1,null,is,'spine'),is2=add('spine2',spine2,null,is1,'spine1'),ine=add('neck',neck,null,is2,'spine2');add('head',head,null,ine,'neck');
 for(const sd of ['left','right']){
  const dir=V(sd+'arm',sd+'forearm',1).normalize(),C=new THREE.Quaternion().setFromUnitVectors(dir,new THREE.Vector3(0,-1,0));
  const upper=mk(V('spine2',sd+'arm')),fore=mk(V(sd+'arm',sd+'forearm').applyQuaternion(C)),hand=mk(V(sd+'forearm',sd+'hand').applyQuaternion(C));
  spine2.add(upper);upper.add(fore);fore.add(hand);
  const side=D(sd+'arm').p.x>=0?1:-1;arms.push({upper,fore,hand,side});
  const ia=add(sd+'arm',upper,C,is2,'spine2'),ifo=add(sd+'forearm',fore,C,ia,sd+'arm');add(sd+'hand',hand,C,ifo,sd+'forearm');
  const lu=mk(V('hips',sd+'upleg')),lo=mk(V(sd+'upleg',sd+'leg')),ft=mk(V(sd+'leg',sd+'foot'));
  hips.add(lu);lu.add(lo);lo.add(ft);legs.push({upper:lu,lower:lo,foot:ft,side:D(sd+'upleg').p.x>=0?1:-1});
  const iu=add(sd+'upleg',lu,null,ih,'hips'),il=add(sd+'leg',lo,null,iu,sd+'upleg');add(sd+'foot',ft,null,il,sd+'leg');
 }
 m.proxyRoot=proxyRoot;m.rig=hips;m.bone={hips,spine,spine1,spine2,neck,head};m.arms=arms;m.legs=legs;
 m.mx={list,f,hipsBone:bones.hips};
 m.ankle=D('leftfoot').p.y*f+.004;m.lieY=.18;
 return m;
}
function mnSyncSkeleton(m){
 const X=m.mx,list=X.list;
 for(let i=0;i<list.length;i++){
  const e=list[i];e.proxy.getWorldQuaternion(e.dq);
  e.W.copy(e.dq).multiply(e.C).multiply(e.R);
  if(e.parentIdx<0)e.bone.quaternion.copy(e.W);
  else{_mnPW.copy(list[e.parentIdx].W);if(e.K)_mnPW.multiply(e.K);e.bone.quaternion.copy(_mnPW.invert()).multiply(e.W);}
 }
 X.hipsBone.position.copy(m.rig.position).multiplyScalar(1/X.f);
}
// MONSTER-ANIM-END
// ---- swap the procedural monsters for the embedded skinned characters -------------------------------------------------
const MN_MODEL_IDS={brute:'monsterModelBrute',stalker:'monsterModelStalker',spitter:'monsterModelSpitter'};
function mnBoneKey(o){return erikaNormName(o.name).replace(/^mixamorig/,'');}
async function loadMonsterModels(M,loaderModule){
 const SU=await import('./vendor/three/examples/jsm/utils/SkeletonUtils.js');
 const loader=new loaderModule.FBXLoader(),protos={};
 for(const type of Object.keys(MN_MODEL_IDS)){
  const node=document.getElementById(MN_MODEL_IDS[type]);if(!node)continue;
  try{
   const model=loader.parse(erikaB64(node.textContent.trim()),'');node.remove();
   model.position.set(0,0,0);model.quaternion.identity();model.scale.set(1,1,1);model.updateMatrixWorld(true);
   const bones={},desc={};
   model.traverse(o=>{if(o.isBone){const n=mnBoneKey(o);if(!bones[n])bones[n]=o;}});
   for(const n in bones){desc[n]={p:bones[n].getWorldPosition(new M.Vector3()),q:bones[n].getWorldQuaternion(new M.Quaternion()),parent:null};}
   for(const n in bones){const par=bones[n].parent;if(par&&par.isBone){const pn=mnBoneKey(par);if(desc[pn])desc[n].parent=pn;}}
   protos[type]={model,desc};
   if(type==='stalker'){try{stalkerPrepareModel(model);}catch(e2){console.warn('Stalker hands tint failed:',e2);}}
  }catch(err){console.warn('Monster model could not be loaded:',type,err);}
 }
 globalThis.MN_SWAP={M,SU,protos};   // kept so monsters spawned later get the same skinned model
 for(const m of monsters){const pr=protos[m.type];if(!pr)continue;try{mnSwapToModel(M,SU,m,pr);}catch(err){console.warn('Monster model swap failed, keeping the procedural body:',m.type,err);}}
}
function mnSwapToModel(M,SU,m,pr){
 const inst=SU.clone(pr.model),bones={};
 inst.traverse(o=>{if(o.isBone){const n=mnBoneKey(o);if(!bones[n])bones[n]=o;}});
 const D=pr.desc,legLen=D.leftupleg.p.distanceTo(D.leftleg.p)+D.leftleg.p.distanceTo(D.leftfoot.p),f=1.04/legLen;   // same leg length the animation was tuned for
 const oldRig=m.rig,oldMeshes=m.hitMeshes;
 mnBuildModelRig(m,D,bones,f);                         // may throw -> caller keeps the procedural monster
 m.root.remove(oldRig);
 for(const mesh of oldMeshes){const i=monsterHitMeshes.indexOf(mesh);if(i>=0)monsterHitMeshes.splice(i,1);}
 m.hitMeshes=[];
 const holder=new M.Group();holder.name='MonsterModel';holder.scale.setScalar(f);holder.add(inst);m.root.add(holder);m.model=holder;
 inst.traverse(o=>{
  if(!(o.isMesh||o.isSkinnedMesh))return;
  o.userData.monster=m;o.castShadow=true;o.receiveShadow=false;o.frustumCulled=false;
  const list=Array.isArray(o.material)?o.material:[o.material];
  for(const mt of list){if(!mt)continue;for(const key of ['color','emissive','specular']){const c=mt[key];if(c&&!(Number.isFinite(c.r)&&Number.isFinite(c.g)&&Number.isFinite(c.b)&&c.r<=1&&c.g<=1&&c.b<=1))c.set(key==='color'?0xffffff:key==='emissive'?0x000000:0x222222);}
   if(mt.map)mt.map.colorSpace=M.SRGBColorSpace;if(mt.emissiveMap)mt.emissiveMap.colorSpace=M.SRGBColorSpace;mt.needsUpdate=true;}
  m.hitMeshes.push(o);monsterHitMeshes.push(o);
 });
 mnInit(m);m.root.updateMatrixWorld(true);
 if(m.type==='stalker'){try{stalkerFxAttach(m,bones.head,D.head,f);}catch(err){console.warn('Stalker skull failed:',err);}}
}
// ===================== NIGHT STALKER DETAILS: bone skull, jaw that opens, red mouth beam, dark-red hands =====================
// The stalker is the embedded skinned "Survivor" model. Everything below is layered on top of it:
//  * the hands are tinted dark red by a per-vertex mask built from the skin weights of the hand / finger bones (shader patch, no extra mesh)
//  * a bone skull (cranium, brow, cheeks, sockets, nose, teeth, horns) and a separate jaw are parented to the real head bone (units: cm, head-joint space)
//  * the eyes glow, and while the stalker attacks its jaw drops open and a red beam shoots from its mouth at its target
// Tweak live from the console, e.g.  STALKER_FX.beamMax=14   STALKER_FX.jawOpen=.8   STALKER_FX.handRGB=[.5,.02,.03]
const STALKER_FX={beamMax:8,beamCore:.05,beamShell:.14,jawOpen:.62,handRGB:[.30,.012,.016],handGlow:.07,attackFrom:.03,attackTo:.46,skull:true};
let _skShared=null;
const _skFwd=new THREE.Vector3(0,0,1),_skV1=new THREE.Vector3(),_skV2=new THREE.Vector3(),_skV3=new THREE.Vector3(),_skUp=new THREE.Vector3(0,1,0);
const skStep=(a,b,x)=>{const t=Math.min(1,Math.max(0,(x-a)/(b-a)));return t*t*(3-2*t);};
function stalkerMerge(parts){   // bake [geometry, matrix, [r,g,b]] pieces into ONE vertex-coloured geometry (shared by every stalker)
 let np=0,ni=0;for(const p of parts){np+=p[0].attributes.position.count;ni+=p[0].index.count;}
 const pos=new Float32Array(np*3),nor=new Float32Array(np*3),col=new Float32Array(np*3),idx=new Uint32Array(ni),nm=new THREE.Matrix3(),v=new THREE.Vector3();let po=0,io=0;
 for(const [g,mat,c] of parts){
  const p=g.attributes.position,n=g.attributes.normal;nm.getNormalMatrix(mat);
  for(let i=0;i<p.count;i++){
   v.fromBufferAttribute(p,i).applyMatrix4(mat);const o=(po+i)*3;pos[o]=v.x;pos[o+1]=v.y;pos[o+2]=v.z;
   v.fromBufferAttribute(n,i).applyMatrix3(nm).normalize();nor[o]=v.x;nor[o+1]=v.y;nor[o+2]=v.z;col[o]=c[0];col[o+1]=c[1];col[o+2]=c[2];
  }
  for(let i=0;i<g.index.count;i++)idx[io+i]=g.index.getX(i)+po;
  po+=p.count;io+=g.index.count;
 }
 const out=new THREE.BufferGeometry();
 out.setAttribute('position',new THREE.BufferAttribute(pos,3));out.setAttribute('normal',new THREE.BufferAttribute(nor,3));out.setAttribute('color',new THREE.BufferAttribute(col,3));
 out.setIndex(new THREE.BufferAttribute(idx,1));out.computeBoundingSphere();return out;
}
function stalkerFxShared(){
 if(_skShared)return _skShared;
 const sph=new THREE.SphereGeometry(1,20,14),box=new THREE.BoxGeometry(1,1,1),cone=new THREE.ConeGeometry(1,1,6),tor=new THREE.TorusGeometry(1,.2,8,20);
 const BONE=[.86,.82,.72],BONE2=[.66,.61,.52],DARK=[.018,.006,.006],TOOTH=[.95,.92,.82];
 const E=(g,x,y,z,sx,sy,sz,col,rx=0,ry=0,rz=0)=>[g,new THREE.Matrix4().compose(new THREE.Vector3(x,y,z),new THREE.Quaternion().setFromEuler(new THREE.Euler(rx,ry,rz)),new THREE.Vector3(sx,sy,sz)),col];
 // ---- static part of the skull (cm, relative to the head joint; +y up, +z forward). It stands a couple of cm proud of the real face so nothing pokes through.
 const sk=[
  E(sph,0,9.8,4.0,11.8,11.2,16.5,BONE),                                  // cranium
  E(sph,0,1.6,10.6,6.4,3.5,8.4,BONE),                                    // upper jaw / muzzle
  E(sph,-6.3,3.4,14.2,2.6,1.5,2.8,BONE2),E(sph,6.3,3.4,14.2,2.6,1.5,2.8,BONE2),   // cheekbones
  E(sph,-8.4,1.2,3.0,3.0,4.2,6.5,BONE2),E(sph,8.4,1.2,3.0,3.0,4.2,6.5,BONE2),     // jaw hinges (hide the real jaw line)
  E(sph,0,8.2,19.4,2.2,1.6,1.8,BONE2),                                   // brow centre
  E(sph,-4.4,8.3,18.1,4.6,1.5,2.6,BONE2,0,0,.22),E(sph,4.4,8.3,18.1,4.6,1.5,2.6,BONE2,0,0,-.22),   // brow ridges, slanted into a scowl
  E(sph,-4.6,5.0,17.3,3.1,2.7,1.4,DARK),E(sph,4.6,5.0,17.3,3.1,2.7,1.4,DARK),     // eye sockets
  E(tor,-4.6,5.0,17.9,3.3,2.9,2.4,BONE2),E(tor,4.6,5.0,17.9,3.3,2.9,2.4,BONE2),   // raised socket rims
  E(sph,0,4.0,18.2,1.1,1.8,1.2,BONE),E(sph,0,2.7,18.3,1.5,2.0,1.1,DARK),          // nose bridge + nasal hole
  E(sph,0,-.8,11.0,4.6,1.6,5.4,DARK),                                    // dark mouth interior (seen when the jaw drops)
  E(cone,0,19.6,2,1.3,5.5,1.3,BONE2,-.15),E(cone,0,19.2,-4.5,1.2,5,1.2,BONE2,-.55),E(cone,0,16.2,-10,1.1,4.4,1.1,BONE2,-.95),   // crest of spikes
  E(cone,-8.2,16.5,1.5,1.2,6,1.2,BONE2,0,0,.55),E(cone,8.2,16.5,1.5,1.2,6,1.2,BONE2,0,0,-.55)   // short horns
 ];
 for(let i=0;i<8;i++){const x=(i-3.5)*1.0,c=(i===0||i===7);sk.push(E(box,x,c?-.9:-.5,17.9-.07*x*x,.95,c?2.3:1.7,.8,TOOTH));}   // upper teeth (outer ones are fangs)
 // ---- lower jaw: its own mesh, pivots at the hinge
 const jw=[E(sph,0,-4.4,7.6,6.0,2.4,8.4,BONE2)];
 for(let i=0;i<7;i++){const x=(i-3)*1.05,c=(i===0||i===6);jw.push(E(box,x,c?-2.6:-3.0,15.4-.07*x*x,.95,c?2.2:1.5,.8,TOOTH));}
 const eyeGeo=stalkerMerge([E(sph,-4.6,5.0,18.7,1.15,1.0,.75,[1,1,1]),E(sph,4.6,5.0,18.7,1.15,1.0,.75,[1,1,1])]);
 _skShared={
  skullGeo:stalkerMerge(sk),jawGeo:stalkerMerge(jw),eyeGeo,
  skullMat:new THREE.MeshStandardMaterial({vertexColors:true,roughness:.82,metalness:0,emissive:0x240606,emissiveIntensity:.55}),
  eyeMat:new THREE.MeshBasicMaterial({color:0xff2412,fog:false}),
  beamGeo:(()=>{const g=new THREE.CylinderGeometry(1,1,1,14,1,true);g.translate(0,.5,0);return g;})(),
  glowTex:(typeof hfxTexSafe==='function')?hfxTexSafe():null
 };
 return _skShared;
}
// ---- hands: tint the hand / finger vertices dark red (called once, on the prototype model, before it is cloned)
function stalkerPrepareModel(model){
 const mats=new Set();
 model.traverse(o=>{
  if(!o.isSkinnedMesh||!o.geometry||!o.skeleton)return;
  const g=o.geometry,si=g.attributes.skinIndex,sw=g.attributes.skinWeight;if(!si||!sw)return;
  if(!g.attributes.handMask){
   const isHand=o.skeleton.bones.map(b=>/hand/i.test(b.name)),n=si.count,mask=new Float32Array(n);
   for(let i=0;i<n;i++){
    const ix=[si.getX(i),si.getY(i),si.getZ(i),si.getW(i)],wt=[sw.getX(i),sw.getY(i),sw.getZ(i),sw.getW(i)];let s=0;
    for(let k=0;k<4;k++)if(isHand[ix[k]])s+=wt[k];
    mask[i]=Math.min(1,Math.max(0,(s-.1)/.55));
   }
   g.setAttribute('handMask',new THREE.BufferAttribute(mask,1));
  }
  for(const mt of (Array.isArray(o.material)?o.material:[o.material]))if(mt)mats.add(mt);
 });
 for(const mt of mats){
  const prev=mt.onBeforeCompile;
  mt.onBeforeCompile=function(shader,renderer){
   if(prev)prev.call(this,shader,renderer);
   shader.uniforms.skHand={value:new THREE.Vector4(STALKER_FX.handRGB[0],STALKER_FX.handRGB[1],STALKER_FX.handRGB[2],STALKER_FX.handGlow)};
   shader.vertexShader=shader.vertexShader.replace('#include <common>','#include <common>\nattribute float handMask;\nvarying float vSkHand;').replace('#include <begin_vertex>','#include <begin_vertex>\nvSkHand=handMask;');
   shader.fragmentShader=shader.fragmentShader.replace('#include <common>','#include <common>\nvarying float vSkHand;\nuniform vec4 skHand;')
    .replace('#include <color_fragment>','#include <color_fragment>\n{float lum=dot(diffuseColor.rgb,vec3(.299,.587,.114));diffuseColor.rgb=mix(diffuseColor.rgb,skHand.rgb*(.55+1.25*lum),clamp(vSkHand,0.,1.));}')
    .replace('#include <emissivemap_fragment>','#include <emissivemap_fragment>\ntotalEmissiveRadiance+=vec3(skHand.a,0.,0.)*vSkHand;');
  };
  const key='stalkerHands';const prevKey=mt.customProgramCacheKey;mt.customProgramCacheKey=function(){return (prevKey?prevKey.call(this):'')+key;};
  mt.needsUpdate=true;
 }
}
// ---- skull, eyes, mouth glow and beam, parented to the real head bone of ONE stalker
function stalkerFxAttach(m,headBone,headDesc,f){
 if(!headBone||!headDesc||!STALKER_FX.skull)return;
 const S=stalkerFxShared(),g=new THREE.Group();g.name='StalkerFace';headBone.add(g);
 g.quaternion.copy(headDesc.q).invert();   // bone frame -> rest frame: +y is up and +z is the face direction whatever the bone axes are
 m.root.updateMatrixWorld(true);
 const ws=new THREE.Vector3().setFromMatrixScale(headBone.matrixWorld);g.scale.setScalar(ws.x>1e-6?(m.cfg.scale*f)/ws.x:1);   // 1 unit of g = 1 cm of the model
 const X={g,mpu:m.cfg.scale*f,t:Math.random()*50,seed:Math.random()*6.28,env:0,life:1};
 const skull=new THREE.Mesh(S.skullGeo,S.skullMat);skull.frustumCulled=false;skull.castShadow=false;g.add(skull);
 const jaw=new THREE.Group();jaw.position.set(0,1.0,2.0);g.add(jaw);X.jaw=jaw;
 const jm=new THREE.Mesh(S.jawGeo,S.skullMat);jm.frustumCulled=false;jaw.add(jm);   // the jaw geometry is authored relative to its hinge
 const eyes=new THREE.Mesh(S.eyeGeo,S.eyeMat);eyes.frustumCulled=false;g.add(eyes);X.eyes=eyes;
 const spr=(sx,y,z,size,col)=>{const s=new THREE.Sprite(new THREE.SpriteMaterial({map:S.glowTex,color:col,transparent:true,opacity:0,depthWrite:false,blending:THREE.AdditiveBlending,fog:false}));s.position.set(sx,y,z);s.scale.setScalar(size);s.frustumCulled=false;s.renderOrder=17;g.add(s);return s;};
 X.eyeL=spr(-4.6,5.0,19.6,7,0xff2a14);X.eyeR=spr(4.6,5.0,19.6,7,0xff2a14);X.mouth=spr(0,-.8,18.6,9,0xff1a0c);
 const beam=new THREE.Group();beam.position.set(0,-.8,18.4);beam.visible=false;g.add(beam);X.beam=beam;
 const bm=(col,op)=>new THREE.MeshBasicMaterial({color:col,transparent:true,opacity:op,depthWrite:false,blending:THREE.AdditiveBlending,side:THREE.DoubleSide,fog:false});
 X.shell=new THREE.Mesh(S.beamGeo,bm(0xff1a0c,.55));X.core=new THREE.Mesh(S.beamGeo,bm(0xffd8c8,.95));
 for(const o of [X.shell,X.core]){o.frustumCulled=false;o.renderOrder=18;beam.add(o);}
 X.tip=new THREE.Sprite(new THREE.SpriteMaterial({map:S.glowTex,color:0xff2a14,transparent:true,opacity:0,depthWrite:false,blending:THREE.AdditiveBlending,fog:false}));X.tip.frustumCulled=false;X.tip.renderOrder=18;beam.add(X.tip);
 m.sfx=X;
}
function stalkerFxUpdate(m,dt){
 const X=m.sfx;if(!X)return;
 const A=m.anim,alive=m.alive&&!m.dead,near=m.rig.visible!==false;
 X.t+=dt;
 let env=0;
 if(alive&&A&&A.attackT>=0&&!m.down&&!m.entry&&!m.climb)env=skStep(STALKER_FX.attackFrom,STALKER_FX.attackFrom+.09,A.attackT)*(1-skStep(STALKER_FX.attackTo-.12,STALKER_FX.attackTo,A.attackT));
 X.env+=(env-X.env)*(1-Math.exp(-(env>X.env?45:20)*dt));
 X.life+=((alive?1:0)-X.life)*(1-Math.exp(-5*dt));
 const flick=.82+.18*Math.sin(X.t*21+X.seed)*Math.sin(X.t*6.1+X.seed*2),eg=(.5+.5*X.env)*flick*X.life;
 X.jaw.rotation.x=STALKER_FX.jawOpen*X.env+(.05+.03*Math.sin(X.t*4.3+X.seed))*X.life;
 X.eyes.visible=X.life>.12;
 X.eyeL.material.opacity=X.eyeR.material.opacity=Math.min(1,eg);X.eyeL.scale.setScalar(5.5+3*X.env);X.eyeR.scale.setScalar(5.5+3*X.env);
 X.mouth.material.opacity=Math.min(1,(.18+.9*X.env)*X.life)*(.9+.1*flick);X.mouth.scale.setScalar(6+9*X.env);
 if(X.env<.02||!near||!(X.life>.5)){X.beam.visible=false;return;}
 // beam: from the mouth straight at the target (clamped so it can never swing back through the head)
 const tw=m.target==='woman'&&CAPTIVE.alive,tx=tw?CAPTIVE.x:player.pos.x,tz=tw?CAPTIVE.z:player.pos.z,ty=(tw?0:player.pos.y)+1.15;
 X.g.updateWorldMatrix(true,false);
 _skV1.set(tx,ty,tz);X.g.worldToLocal(_skV1);_skV1.sub(X.beam.position);
 let len=_skV1.length()||1;_skV2.copy(_skV1).divideScalar(len);
 if(_skV2.z<.3){_skV2.z=.3;_skV2.normalize();}
 const maxL=STALKER_FX.beamMax/X.mpu,L=Math.min(len*1.06,maxL)*Math.min(1,X.env*1.5);
 X.beam.visible=true;X.beam.quaternion.setFromUnitVectors(_skUp,_skV2);
 const pul=1+.14*Math.sin(X.t*70),rc=STALKER_FX.beamCore/X.mpu*pul*X.env,rs=STALKER_FX.beamShell/X.mpu*pul*X.env;
 X.core.scale.set(rc,L,rc);X.shell.scale.set(rs,L,rs);X.core.material.opacity=.95*X.env;X.shell.material.opacity=.55*X.env;
 X.tip.position.set(0,L,0);X.tip.scale.setScalar(26*X.env/ (X.mpu*60));X.tip.material.opacity=Math.min(1,X.env);
 if(HFX.ready&&dt>0&&X.env>.4){   // embers spraying from the mouth
  X.beam.getWorldPosition(_skV3);_skV1.set(0,0,0);
  const fwd=_skV2.clone().applyQuaternion(X.g.getWorldQuaternion(new THREE.Quaternion()));
  for(let i=0;i<2;i++){_dfx.v.copy(fwd).multiplyScalar(5+Math.random()*7);_dfx.v.x+=(Math.random()-.5)*3;_dfx.v.y+=(Math.random()-.5)*3;_dfx.v.z+=(Math.random()-.5)*3;dashSpark(_skV3,_dfx.v,.18+Math.random()*.18,.08+Math.random()*.1,i?0xff3a22:0xffc0a0);}
 }
}
function startMonsterAttack(m,cooldown){
 playMonsterAsset('monster',m);const A=m.anim;A.attackT=0;A.struck=false;A.attackSide=Math.random()<.5?-1:1;m.attackCooldown=cooldown;m.attackSerial++;}
// The blow lands (or the spit leaves the mouth) at the exact moment the animation reaches the strike, so it can be dodged.
function stepMonsterAttack(m,dt,dist,dy,tw){
 const A=m.anim,P=MN_PARAMS[m.type];if(A.hitDelay>0)return;   // just hit by the sword: the blow is delayed 0.2 s
 A.attackT+=dt;
 if(!A.struck&&A.attackT>=P.atk.hit){
  A.struck=true;
  if(monsterRespawnTimer<=0||tw){
   if(m.type==='spitter')launchMonsterSpit(m);
   else if(dist<=m.cfg.range*1.3&&Math.abs(dy)<m.cfg.scale*2.6){if(tw)damageCaptive(m.cfg.damage*.9);else damagePlayer(m.cfg.damage*BAL.dmgMul(),m.root.position);}
  }
 }
 if(A.attackT>=P.atk.dur)A.attackT=-1;
}
function applyMonsterKnock(m,dt){
 const A=m.anim;if(!A.knockX&&!A.knockZ)return;
 const nx=m.root.position.x+A.knockX*dt,nz=m.root.position.z+A.knockZ*dt;
 if(monsterSpotFree(nx,nz,.48*m.cfg.scale)){m.root.position.x=nx;m.root.position.z=nz;}else{A.knockX=0;A.knockZ=0;}
 const k=Math.exp(-6*dt);A.knockX*=k;A.knockZ*=k;if(Math.abs(A.knockX)+Math.abs(A.knockZ)<.03){A.knockX=0;A.knockZ=0;}
}
function mnCull(m){   // PERF: hide the skinned model itself (not just the proxy rig) when it is off-screen or too far -> no draw call, no skeleton upload
 const p=m.root.position,sc=m.cfg.scale,sp=HFR.s,pd=Math.hypot(player.pos.x-p.x,player.pos.z-p.z);
 sp.center.set(p.x,p.y+1.6*sc,p.z);sp.radius=3.2*sc;
 const vis=pd<HORDE.drawDist&&HFR.fr.intersectsSphere(sp);
 if(m.rig.visible!==vis)m.rig.visible=vis;if(m.model&&m.model.visible!==vis)m.model.visible=vis;
 return vis;
}
function updateMonsters(dt){
 updateMonsterAudioVolumes();if(!monsterMaterials)return;playerHurtCooldown=Math.max(0,playerHurtCooldown-dt);if(monsterHurtFlash)monsterHurtFlash.style.opacity=String(Math.max(0,Number(monsterHurtFlash.style.opacity)-dt*2.6));
 if(monsterRespawnTimer>0){monsterRespawnTimer-=dt;if(monsterRespawnTimer<=0){resetPlayer();showToast('BACK IN THE HUNT');}}
 MNP.budget=MNP.perFrame;bossUpdate(dt);hordeUpdate(dt);HFR.fr.setFromProjectionMatrix(HFR.m.multiplyMatrices(camera.projectionMatrix,camera.matrixWorldInverse));
 for(const m of monsters){
  const A=m.anim;if(!A)continue;
  if(m.dead&&!m.root.visible)continue;
  if(m.sfx)stalkerFxUpdate(m,dt);
  if(m.dead){if(m.shOn){m.shOn=false;for(const o of m.hitMeshes)o.castShadow=false;}mnCull(m);m.deadTimer-=dt;if(m.rd)mnRagdollStep(m,dt);else{applyMonsterKnock(m,dt);mnAnimateDeath(m,dt);}if(m.deadTimer<=0){m.root.visible=false;m.rd=null;}m.root.updateMatrixWorld(true);continue;}
  if(!m.alive)continue;
  m.attackCooldown=Math.max(0,m.attackCooldown-dt);m.recoil=Math.max(0,m.recoil-dt);A.stun=Math.max(0,A.stun-dt);A.hitDelay=Math.max(0,(A.hitDelay||0)-dt);
  applyMonsterKnock(m,dt);
  if(m.down){monsterDownStep(m,dt);m.root.updateMatrixWorld(true);continue;}
  const tw=m.target==='woman'&&CAPTIVE.alive,tx=tw?CAPTIVE.x:player.pos.x,tz=tw?CAPTIVE.z:player.pos.z,ty=tw?0:player.pos.y;   // 60% hunt the player, 40% go for the captive
  const dx=tx-m.root.position.x,dz=tz-m.root.position.z,dist=Math.hypot(dx,dz),dy=ty-m.root.position.y;
  // smooth turn toward the player (heavy monsters turn slowly, and plant themselves while striking)
  const aim=Math.atan2(dx,dz);if(!A.ready){A.yaw=aim;A.ready=true;}
  const turnK=MN_PARAMS[m.type].turn*(A.attackT>=0&&m.type!=='spitter'?.25:1)*(A.stun>0?.3:1);
  A.yaw+=mnWrap(aim-A.yaw)*(1-Math.exp(-turnK*dt));m.root.rotation.y=A.yaw;
  if(m.entry){const ev=mnCull(m);monsterEntryStep(m,dt);if(ev||((m.cullN=((m.cullN||0)+1)&3)===0))m.root.updateMatrixWorld(true);continue;}
  if(m.climb){monsterClimbStep(m,dt);m.root.updateMatrixWorld(true);continue;}
  mnSettleY(m,dt);
  if(A.attackT>=0)stepMonsterAttack(m,dt,dist,dy,tw);
  if(A.attackT<0&&A.stun<=0){
   if(m.type==='spitter'){
    if(dist<22&&dist>3.5&&Math.abs(dy)<28&&m.attackCooldown<=0&&(monsterRespawnTimer<=0||tw))startMonsterAttack(m,2.35);
    else if(dist>12)moveMonsterAuto(m,tx,tz,dt,tw);
    else if(dist<5.5)moveMonsterToward(m,m.root.position.x-dx,m.root.position.z-dz,dt);
   }else if(dist>m.cfg.range*.92)moveMonsterAuto(m,tx,tz,dt,tw);
   else if(Math.abs(dy)<m.cfg.scale*2.3&&m.attackCooldown<=0&&(monsterRespawnTimer<=0||tw))startMonsterAttack(m,m.cfg.cooldown);
  }
  {const p=m.root.position,sc=m.cfg.scale,sp=HFR.s,pd=Math.hypot(player.pos.x-p.x,player.pos.z-p.z);sp.center.set(p.x,p.y+1.6*sc,p.z);sp.radius=3.2*sc;
   const vis=pd<HORDE.drawDist&&HFR.fr.intersectsSphere(sp);if(m.rig.visible!==vis)m.rig.visible=vis;if(m.model&&m.model.visible!==vis)m.model.visible=vis;m.farHidden=!vis&&pd>HORDE.lodDist;
   if(!vis){A.lastX=p.x;A.lastZ=p.z;}
   else if(pd>HORDE.lodDist){m.lodAcc=(m.lodAcc||0)+dt;m.lodN=((m.lodN||0)+1)%3;if(m.lodN===0){mnAnimate(m,m.lodAcc);m.lodAcc=0;}}
   else if(pd>HORDE.midDist){m.lodAcc=(m.lodAcc||0)+dt;m.lodN=((m.lodN||0)+1)%2;if(m.lodN===0){mnAnimate(m,m.lodAcc);m.lodAcc=0;}}
   else{m.lodAcc=0;mnAnimate(m,dt);}
   const sh=vis&&pd<HORDE.shadowDist;if(m.shOn!==sh){m.shOn=sh;for(const o of m.hitMeshes)o.castShadow=sh;}}
  if(!m.farHidden||((m.cullN=((m.cullN||0)+1)&3)===0))m.root.updateMatrixWorld(true);
 }
 monsterBodyBlock();updateMonsterProjectiles(dt);updateMonsterSwordHits();monsterHudTimer-=dt;if(monsterHudTimer<=0){monsterHudTimer=.12;updateMonsterHUD();}
}
// ===================== WALL ENTRY: monsters leap over the city wall from random directions =====================
// Tweak live: WALL_ENTRY.gap=1  (seconds between arrivals)   WALL_ENTRY.flight=[1.5,2]  (jump duration)   WALL_ENTRY.landMin / landMax (landing distance inside the wall, m)
const WALL_ENTRY={gravity:26,firstDelay:1.5,gap:2.6,jitter:2.5,flight:[1.9,2.6],landMin:20,landMax:45};
function startWallEntry(m,idx){
 const a=Math.random()*Math.PI*2,r=WORLD.wallRadius;
 m.root.position.set(Math.cos(a)*r,WORLD.wallHeight,Math.sin(a)*r);m.root.visible=true;assignMonsterTarget(m);m.climb=null;m.roof=null;m.detour=null;m.path=null;m.forcePlan=false;m.stk=null;
 m.entry={phase:'wait',a,t:WALL_ENTRY.firstDelay+idx*WALL_ENTRY.gap+Math.random()*WALL_ENTRY.jitter,vel:new THREE.Vector3()};
}
function wallEntryLand(m){
 const e=m.entry,W=WALL_ENTRY;
 for(let i=0;i<14;i++){const aa=e.a+(Math.random()-.5)*.5,rr=WORLD.wallRadius-W.landMin-Math.random()*(W.landMax-W.landMin),x=Math.cos(aa)*rr,z=Math.sin(aa)*rr;if(monsterSpotFree(x,z,1.4*m.cfg.scale))return [x,z];}
 return [Math.cos(e.a)*(WORLD.wallRadius-W.landMin),Math.sin(e.a)*(WORLD.wallRadius-W.landMin)];
}
// Leap animation: anticipation crouch -> explosive launch (arms swing overhead, body stretches) -> tucked flight -> legs reach down & arms flare to brace -> landing squash -> recover.
// Key = [hipHeight x idleHip, spineLean, armPitch, armOut, elbow, footLift, footForward, hipPitch]; the live pose eases toward the key of the current phase, so transitions stay fluid.
function mnLeapKeys(m){const P=MN_PARAMS[m.type],rest=P.lean*.72-.08;return{
 IDLE:[1,P.lean,rest,P.armOut,-.25,0,0,0],
 CROUCH:[.6,.55,.8,.3,-.6,0,.05,.12],
 LAUNCH:[1.1,-.12,-2.7,.5,-.15,.3,-.18,-.1],
 AIR:[.95,.35,-1.7,.95,-.75,.55,.25,.2],
 FALL:[1.02,.02,-2.2,1.1,-.3,.16,.32,-.05],
 LAND:[.55,.55,-.1,.5,-.45,0,.12,.15]};}
function mnLeapApply(m,dt,K,rate){
 const A=m.anim,P=MN_PARAMS[m.type],pose=A.pose;A.t+=dt;
 const L=A.leap||(A.leap=mnLeapKeys(m).IDLE.slice());
 for(let i=0;i<K.length;i++)L[i]=mnDamp(L[i],K[i],rate,dt);
 const hipM=L[0],lean=L[1],ux=L[2],out=L[3],fore=L[4],lift=L[5],fz=L[6],hp=L[7];
 for(let i=0;i<2;i++){const s=i?1:-1;A.foot[i].set(s*(m.hipW+.045+lift*.15),m.ankle+lift,fz+s*.1*lift);A.zN[i+2]=-.25*lift;}
 let hy=P.idleHip*hipM+m.hipOff;const R=.985*m.legReach;
 for(let i=0;i<2;i++){const T=A.foot[i],up=m.legS[i].upper.position,hh=Math.hypot(T.x-up.x,T.z-up.z);hy=Math.min(hy,T.y+Math.sqrt(Math.max(0,R*R-hh*hh))-up.y);}
 hy=Math.max(hy,.5+m.hipOff);
 pose.h[0]=0;pose.h[1]=hy;pose.h[2]=0;pose.h[3]=hp;pose.h[4]=0;pose.h[5]=0;
 for(let k=0;k<3;k++){pose.s[k*3]=lean*(k?.33:.34);pose.s[k*3+1]=0;pose.s[k*3+2]=0;}
 pose.n[0]=-lean*.15;pose.n[1]=0;pose.n[2]=0;pose.hd[0]=-lean*.65;pose.hd[1]=0;pose.hd[2]=0;
 for(let i=0;i<2;i++){const s=i?1:-1,q=pose.a[i];q[0]=ux+s*.12;q[1]=0;q[2]=s*out;q[3]=fore;q[4]=-.25;}
 for(let i=0;i<2;i++){const f=pose.f[i],T=A.foot[i];f[0]=T.x;f[1]=T.y;f[2]=T.z;f[3]=A.zN[i+2];f[4]=0;}
 mnApplyPose(m,pose);
}
function monsterEntryStep(m,dt){
 const e=m.entry,p=m.root.position,g=WALL_ENTRY.gravity,A=m.anim,K=mnLeapKeys(m);
 const face=()=>{const hd=Math.atan2(e.vel.x,e.vel.z);A.yaw+=mnWrap(hd-A.yaw)*(1-Math.exp(-12*dt));m.root.rotation.y=A.yaw;};
 if(e.phase==='wait'){e.t-=dt;if(m.rig.visible!==false)mnAnimate(m,dt);if(e.t>0)return;
  const [lx,lz]=wallEntryLand(m),F=WALL_ENTRY.flight,T=F[0]+Math.random()*(F[1]-F[0]);
  e.vel.set((lx-p.x)/T,(m.spawn.y-p.y+.5*g*T*T)/T,(lz-p.z)/T);e.T=T;e.phase='crouch';e.c=0;A.leap=K.IDLE.slice();return;}
 if(e.phase==='crouch'){e.c+=dt;face();mnLeapApply(m,dt,K.CROUCH,9);if(e.c>=.42){e.phase='jump';e.tj=0;}return;}
 if(e.phase==='jump'){
  e.tj+=dt;e.vel.y-=g*dt;p.addScaledVector(e.vel,dt);face();const u=e.tj/e.T;
  mnLeapApply(m,dt,u<.16?K.LAUNCH:u<.58?K.AIR:K.FALL,u<.16?22:7);
  if(p.y<=m.spawn.y&&e.vel.y<0){   // touchdown: dust ring, camera kick if the player is near, landing squash
   p.y=m.spawn.y;e.phase='land';e.c=0;
   if(HFX.ready){const sc=m.cfg.scale,q=new THREE.Vector3(p.x,p.y+.4,p.z);hfxPut(HFX.rings,q,.5,1*sc,12*sc,0xffd9a0);hfxPut(HFX.flashes,q,.2,3*sc,6,0xffe2b0);}
   const d=Math.hypot(p.x-player.pos.x,p.z-player.pos.z);if(d<50)slamFx.shake=Math.max(slamFx.shake||0,.28*(1-d/50));}
  return;}
 e.c+=dt;mnLeapApply(m,dt,e.c<.14?K.LAND:K.IDLE,e.c<.14?26:8);
 if(e.c>=.5){m.entry=null;A.lastX=p.x;A.lastZ=p.z;A.stun=.1;m.attackCooldown=.6;}
}
// ===================== HORDE: the longer the game lasts, the more monsters arrive =====================
// Tweak live: HORDE.base=15 (monsters alive at start)  HORDE.perSec=.2 (extra monsters per second of play)  HORDE.cap=40 (max alive; heavy for the GPU above ~50)
// Performance: monsters outside the camera view or beyond drawDist are hidden and not animated; beyond lodDist they animate at 1/3 rate; only monsters within shadowDist cast shadows.
const HORDE={t:0,spawnT:0,base:14,perSec:.12,cap:50,start:6,lodDist:55,midDist:28,drawDist:150,shadowDist:40};
const HFR={fr:new THREE.Frustum(),m:new THREE.Matrix4(),s:new THREE.Sphere()};
function hordeTarget(){return Math.min(HORDE.cap,HORDE.base+Math.floor(HORDE.t*HORDE.perSec));}
function monsterRayCandidates(o,reach){const out=[],r2=reach*reach;for(const m of monsters){if(!m.alive)continue;const p=m.root.position,dx=p.x-o.x,dy=p.y+1.5-o.y,dz=p.z-o.z;if(dx*dx+dy*dy+dz*dz<r2)for(const h of m.hitMeshes)out.push(h);}return out;}
// Body block: alive monsters on the ground cannot overlap each other; heavier (bigger) ones get pushed less.
const MONSTER_BODY=.5;   // body radius per unit of scale
function monsterBodyBlock(){
 const n=monsters.length;
 for(let i=0;i<n;i++){const a=monsters[i];if(!a.alive||a.entry)continue;const pa=a.root.position,ra=MONSTER_BODY*a.cfg.scale;
  for(let j=i+1;j<n;j++){const b=monsters[j];if(!b.alive||b.entry)continue;const pb=b.root.position,rb=MONSTER_BODY*b.cfg.scale;
   const dx=pb.x-pa.x,dz=pb.z-pa.z,min=ra+rb;if(dx>min||dx<-min||dz>min||dz<-min)continue;
   const d2=dx*dx+dz*dz;if(d2>=min*min||Math.abs(pb.y-pa.y)>2)continue;
   let d=Math.sqrt(d2),nx,nz;if(d<1e-4){const ang=(i*2.399+j)%6.283;nx=Math.cos(ang);nz=Math.sin(ang);d=0;}else{nx=dx/d;nz=dz/d;}
   const over=min-d,wa=b.cfg.scale*b.cfg.scale,wb=a.cfg.scale*a.cfg.scale,ws=wa+wb;   // share of the push each one takes (the lighter moves more)
   const ax=pa.x-nx*over*wa/ws,az=pa.z-nz*over*wa/ws,bx=pb.x+nx*over*wb/ws,bz=pb.z+nz*over*wb/ws;
   if(monsterSpotFree(ax,az,.48*a.cfg.scale)){pa.x=ax;pa.z=az;}
   if(monsterSpotFree(bx,bz,.48*b.cfg.scale)){pb.x=bx;pb.z=bz;}}}
}
// ===================== CAPTIVE WOMAN: tied to a post in the middle of the map, 40% of the monsters go for her =====================
// Tweak: CAPTIVE.max (her health), CAPTIVE_SHARE (fraction of monsters that target her), CLIMB.speed / CLIMB.minDy (monster wall climbing)
const CAPTIVE={x:0,z:0,hp:600,max:600,size:1.8,failT:0,warnT:0,alive:true,group:null,P:{},flinch:0,under:0,t:0,el:null,fill:null,txt:null,nW:0,nT:0};
const CAPTIVE_SHARE=.3,CLIMB={speed:4.14,minDy:3.5};
function captiveBuild(){
 const g=new THREE.Group(),M=(c,r=.8)=>new THREE.MeshStandardMaterial({color:c,roughness:r,metalness:0});
 const wood=M(0x4a3426,.9),stone=M(0x6e6a64,.95),skin=M(0xe2b894,.7),cloth=M(0xb64a5a,.85),clothD=M(0x8e3445,.9),hair=M(0x2a1a14,.6),rope=M(0xb89a62,.95),dark=M(0x1b1210,.5);cloth.side=THREE.DoubleSide;
 const add=(geo,mat,x,y,z,parent)=>{const o=new THREE.Mesh(geo,mat);o.position.set(x,y,z);(parent||g).add(o);return o;};
 add(new THREE.CylinderGeometry(.62,.7,.16,20),stone,0,.08,0);
 add(new THREE.CylinderGeometry(.13,.15,2.5,12),wood,0,1.41,-.05);add(new THREE.SphereGeometry(.16,10,8),wood,0,2.68,-.05);
 // lamp on top of the post: iron cage + glowing core + roof, a soft additive glow and a fake pool of light on the ground (no PointLight, keeps the FPS)
 {const iron=M(0x1f1d1b,.5),glass=new THREE.MeshBasicMaterial({color:0xffd58a,fog:false}),LZ=-.05,LY=3.07;
  add(new THREE.CylinderGeometry(.17,.12,.06,12),iron,0,2.84,LZ);add(new THREE.CylinderGeometry(.17,.17,.04,12),iron,0,3.29,LZ);
  add(new THREE.CylinderGeometry(.095,.095,.36,10),glass,0,LY,LZ);
  for(const sx of[-1,1])for(const sz of[-1,1])add(new THREE.BoxGeometry(.024,.42,.024),iron,sx*.115,LY,LZ+sz*.115);
  add(new THREE.ConeGeometry(.24,.2,12),iron,0,3.41,LZ);add(new THREE.SphereGeometry(.04,8,6),iron,0,3.54,LZ);
  const gc=document.createElement('canvas');gc.width=gc.height=128;{const x=gc.getContext('2d'),gr=x.createRadialGradient(64,64,0,64,64,64);gr.addColorStop(0,'rgba(255,255,255,1)');gr.addColorStop(.25,'rgba(255,255,255,.55)');gr.addColorStop(.6,'rgba(255,255,255,.14)');gr.addColorStop(1,'rgba(255,255,255,0)');x.fillStyle=gr;x.fillRect(0,0,128,128);}
  const gt=new THREE.CanvasTexture(gc);gt.colorSpace=THREE.SRGBColorSpace;
  const glow=new THREE.Sprite(new THREE.SpriteMaterial({map:gt,color:0xffb860,transparent:true,opacity:.9,depthWrite:false,blending:THREE.AdditiveBlending,fog:false}));glow.position.set(0,LY,LZ);glow.scale.set(2.4,2.4,1);glow.renderOrder=12;g.add(glow);CAPTIVE.lampGlow=glow;
  const pool=new THREE.Mesh(new THREE.PlaneGeometry(1,1),new THREE.MeshBasicMaterial({map:gt,color:0xffa850,transparent:true,opacity:.42,depthWrite:false,blending:THREE.AdditiveBlending,fog:false,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2}));pool.rotation.x=-Math.PI/2;pool.position.set(0,.05,0);pool.scale.set(3.8,3.8,1);pool.renderOrder=11;g.add(pool);}
 const W=new THREE.Group();W.position.set(0,.16,.3);g.add(W);
 for(const sd of[-1,1]){add(new THREE.CylinderGeometry(.055,.045,.78,8),skin,sd*.09,.45,0,W);add(new THREE.BoxGeometry(.09,.06,.18),clothD,sd*.09,.05,.04,W);}
 const T=new THREE.Group();T.position.set(0,.82,0);W.add(T);
 add(new THREE.CylinderGeometry(.17,.34,.6,16,1,true),cloth,0,-.3,0,T);
 add(new THREE.CylinderGeometry(.14,.17,.5,12),cloth,0,.25,0,T);
 const H=new THREE.Group();H.position.set(0,.52,0);T.add(H);
 add(new THREE.CylinderGeometry(.045,.05,.1,8),skin,0,.05,0,H);
 const head=add(new THREE.SphereGeometry(.115,16,12),skin,0,.2,0,H);head.scale.y=1.12;
 add(new THREE.SphereGeometry(.125,14,10),hair,0,.225,-.03,H);add(new THREE.SphereGeometry(.07,8,6),hair,0,.12,-.14,H);add(new THREE.SphereGeometry(.05,8,6),hair,0,.04,-.17,H);
 for(const sd of[-1,1])add(new THREE.SphereGeometry(.014,6,5),dark,sd*.04,.2,.108,H);
 add(new THREE.BoxGeometry(.04,.01,.01),M(0x9a3a40),0,.15,.112,H);
 const arms={};
 for(const sd of[-1,1]){const A=new THREE.Group();A.position.set(sd*.17,.46,0);A.rotation.x=.55;A.rotation.z=-sd*.12;T.add(A);
  add(new THREE.CylinderGeometry(.04,.036,.26,8),skin,0,-.13,0,A);
  const F=new THREE.Group();F.position.set(0,-.26,0);F.rotation.x=.9;A.add(F);add(new THREE.CylinderGeometry(.034,.03,.24,8),skin,0,-.12,0,F);add(new THREE.SphereGeometry(.04,8,6),skin,0,-.25,0,F);
  arms[sd<0?'L':'R']=A;}
 for(const y of[1.3,1.0,.58]){const r=add(new THREE.TorusGeometry(.3,.022,6,20),rope,0,y,.12);r.rotation.x=Math.PI/2;r.scale.set(.9,1.3,1);}
 CAPTIVE.P={W,T,H,armL:arms.L,armR:arms.R};return g;
}
function captiveHud(){
 const C=CAPTIVE;if(C.el)return;const el=document.createElement('div');el.id='captiveHUD';el.style.display='none';
 el.innerHTML='<div class="ch-row"><span class="ch-ico">&#9829;</span><span class="ch-name">THE CAPTIVE</span><span class="ch-pct cp">600</span></div><div class="ch-bar"><i class="cf"></i></div><div class="ch-sub"><span class="ch-dir"><b class="cd">&#9650;</b></span><span class="cm">0 m</span><span class="ch-tip">PROTECT HER</span></div>';
 document.body.appendChild(el);
 const w=document.createElement('div');w.id='captiveWarn';w.innerHTML='<b>&#9888; THE CAPTIVE IS UNDER ATTACK</b><span>Get to her before she falls!</span>';document.body.appendChild(w);
 const f=document.createElement('div');f.id='captiveFlash';document.body.appendChild(f);
 C.el=el;C.fill=el.querySelector('.cf');C.txt=el.querySelector('.cp');C.dir=el.querySelector('.cd');C.dist=el.querySelector('.cm');C.warn=w;C.flash=f;
 document.getElementById('goRestart').onclick=()=>{document.getElementById('gameOver').classList.add('hidden');resetPlayer();resumeRun();showToast('RUN RESTARTED');};
 document.getElementById('goMenu').onclick=()=>{document.getElementById('gameOver').classList.add('hidden');resetPlayer();goMainMenu();};
}
function captiveSetBar(){const C=CAPTIVE;if(!C.fill)return;const f=C.hp/C.max;C.fill.style.width=(f*100)+'%';C.txt.textContent=Math.ceil(C.hp-1e-6);C.el.dataset.lvl=f>.5?'hi':f>.25?'mid':'low';}
function captiveWarn(){const C=CAPTIVE;if(!C.warn)return;C.warnT=2.6;C.warn.classList.add('show');if(C.flash)C.flash.style.opacity='.9';}
function fmtTime(sec){sec=Math.floor(sec);return String(Math.floor(sec/60)).padStart(2,'0')+':'+String(sec%60).padStart(2,'0');}
function captiveHudUpdate(dt){
 const C=CAPTIVE;if(!C.el)return;
 C.el.style.display=running?'block':'none';
 if(C.warnT>0){C.warnT-=dt;if(C.warnT<=0)C.warn.classList.remove('show');}
 if(C.flash&&C.flash.style.opacity!=='0')C.flash.style.opacity=String(Math.max(0,Number(C.flash.style.opacity)-dt*1.8));
 const f=cameraDir(),dx=C.x-player.pos.x,dz=C.z-player.pos.z,th=Math.atan2(dx*-f.z+dz*f.x,dx*f.x+dz*f.z);   // arrow points toward her, relative to where you look
 C.dir.style.transform='rotate('+(th*57.2958).toFixed(1)+'deg)';C.dist.textContent=Math.round(Math.hypot(dx,dz))+' m';
 C.lt=(C.lt||0)-dt;if(C.lt<=0){C.lt=.5;const tl=document.getElementById('topLabel');if(tl)tl.textContent='KAGE DISTRICT // SIEGE MODE';}
 if(!C.alive&&C.failT>0){C.failT-=dt;if(C.failT<=0&&!playerDeath.active)showGameOver('captive');}
}
function showGameOver(reason){   // the run is lost: 'captive' (default) = she died, 'player' = you died
 {const gt=document.getElementById('goTitle'),gs=document.getElementById('goSub');if(gt&&gs){if(reason==='player'){gt.innerHTML='YOU <span>DIED</span>';gs.textContent='The monsters overwhelmed you. The village is lost.';}else{gt.innerHTML='THE CAPTIVE <span>FELL</span>';gs.textContent='The monsters reached her before you did. The village is lost.';}}}
 running=false;paused=true;try{stopAim();}catch(e){}detachAll(false);if(document.pointerLockElement)document.exitPointerLock();
 document.getElementById('goTime').textContent=fmtTime(HORDE.t);document.getElementById('goKills').textContent=monsterKills;
 document.getElementById('gameOver').classList.remove('hidden');
}
function captiveInit(){
 const C=CAPTIVE;if(C.group)return;
 let spot=null;for(let r=0;r<60&&!spot;r+=4)for(let a=0;a<8&&!spot;a++){const x=Math.cos(a*Math.PI/4)*r,z=Math.sin(a*Math.PI/4)*r;if(monsterSpotFree(x,z,4)&&Math.hypot(x,z-3)>=4.5&&Math.hypot(x,z+3)>=4.5)spot=[x,z];}
 spot=[0,0];C.x=spot[0];C.z=spot[1];   // the captive stands in the middle of the plaza, where the fountain used to be
 const g=captiveBuild();g.position.set(C.x,0,C.z);g.scale.setScalar(C.size);scene.add(g);C.group=g;
 colliders.push({x:C.x,z:C.z,halfX:.55*C.size,halfZ:.55*C.size,top:2.7*C.size,kind:'post'});   // solid for the player and the monsters
 captiveHud();captiveSetBar();
}
function captiveReset(){
 const C=CAPTIVE;C.hp=C.max;C.alive=true;C.flinch=0;C.under=0;C.nW=0;C.nT=0;C.sl=0;C.failT=0;C.warnT=0;if(C.warn)C.warn.classList.remove('show');{const go=document.getElementById('gameOver');if(go)go.classList.add('hidden');}
 if(C.P.W){C.P.W.position.set(0,.16,.3);C.P.W.rotation.set(0,0,0);C.P.T.rotation.set(0,0,0);C.P.H.rotation.set(0,0,0);}
 captiveSetBar();
}
function damageCaptive(a){
 const C=CAPTIVE;if(!C.alive)return;C.hp=Math.max(0,C.hp-a);C.flinch=1;C.under=1.5;captiveWarn();
 if(HFX.ready)hfxPut(HFX.flashes,new THREE.Vector3(C.x,1.3*C.size,C.z+.3*C.size),.14,1.3*C.size,4,0xff9a90);
 if(C.hp<=0){C.alive=false;C.failT=1.8;if(C.warn)C.warn.classList.remove('show');showToast('THE CAPTIVE HAS FALLEN');for(const mm of monsters)mm.target='player';}
 captiveSetBar();
}
function assignMonsterTarget(m){const C=CAPTIVE;if(m.type==='spitter'){m.target='player';return;}let w=false;if(C.alive)w=C.nW<CAPTIVE_SHARE*(C.nT+1);C.nT++;if(w)C.nW++;m.target=w?'woman':'player';}
function captiveUpdate(dt){
 const C=CAPTIVE;if(!C.group)return;C.t+=dt;C.flinch=Math.max(0,C.flinch-dt*2.2);C.under=Math.max(0,C.under-dt);
 captiveHudUpdate(dt);if(C.lampGlow){C.lampGlow.material.opacity=.88+.07*Math.sin(C.t*6.7)+.04*Math.sin(C.t*14.3+1);}
 const P=C.P,t=C.t,hp=C.hp/C.max;
 if(C.model){captiveModelAnim(dt);return;}
 if(C.alive){
  const fear=C.flinch+(1-hp)*.5+C.under*.5,sb=Math.pow(Math.max(0,Math.sin(t*.9)),6)*(.4+fear);   // bursts of struggling, harder when threatened or hurt
  P.T.scale.y=1+.012*Math.sin(t*2.1);P.T.rotation.x=.12*(1-hp)+.03*Math.sin(t*1.7);
  P.H.rotation.x=.08+.04*Math.sin(t*1.3)+.45*C.flinch;P.H.rotation.y=.35*Math.sin(t*.6)+.25*sb*Math.sin(t*19);
  P.W.rotation.z=.05*sb*Math.sin(t*14);P.W.position.x=.012*sb*Math.sin(t*17);
  P.armL.rotation.x=.55+.12*sb*Math.sin(t*15);P.armR.rotation.x=.55+.12*sb*Math.sin(t*15+1.7);
 }else{
  const k=1-Math.exp(-3*dt);   // slumped, hanging in the ropes
  P.H.rotation.x+=(1.05-P.H.rotation.x)*k;P.H.rotation.y+=(0-P.H.rotation.y)*k;P.T.rotation.x+=(.5-P.T.rotation.x)*k;P.W.position.y+=(.08-P.W.position.y)*k;P.W.rotation.z+=(0-P.W.rotation.z)*k;
 }
}
// ===================== MONSTERS CLIMB BUILDINGS (when the player is on a roof they cannot reach) =====================
function mnSettleY(m,dt){const p=m.root.position;if(!m.roof&&!m.climb&&!m.entry&&p.y>m.spawn.y+.02)p.y=Math.max(m.spawn.y,p.y-14*dt);}
function mnClimbApply(m,dt,ph,mu){
 const A=m.anim,P=MN_PARAMS[m.type],pose=A.pose;A.t+=dt;
 const L=A.leap||(A.leap=mnLeapKeys(m).IDLE.slice());
 L[0]=mnDamp(L[0],.84,9,dt);L[1]=mnDamp(L[1],.2,9,dt);L[7]=mnDamp(L[7],.08,9,dt);
 const w=A.cw=mnDamp(A.cw||0,1,9,dt),rest=P.lean*.72-.08;
 for(let i=0;i<2;i++){const sd=i?1:-1,sw=Math.sin(ph+(i?Math.PI:0)),lift=Math.max(0,sw)*(.42+.2*mu)*w;   // legs step up the wall alternately
  A.foot[i].set(sd*(m.hipW+.03),m.ankle+.18*w+lift,.3*w+.1*sw*w);A.zN[i+2]=-.3*w;}
 let hy=P.idleHip*L[0]+m.hipOff+.04*Math.sin(2*ph)*w;const R=.985*m.legReach;
 for(let i=0;i<2;i++){const T=A.foot[i],up=m.legS[i].upper.position,hh=Math.hypot(T.x-up.x,T.z-up.z);hy=Math.min(hy,T.y+Math.sqrt(Math.max(0,R*R-hh*hh))-up.y);}
 hy=Math.max(hy,.5+m.hipOff);
 pose.h[0]=0;pose.h[1]=hy;pose.h[2]=.12*w;pose.h[3]=L[7];pose.h[4]=0;pose.h[5]=0;
 for(let k=0;k<3;k++){pose.s[k*3]=L[1]*(k?.33:.34);pose.s[k*3+1]=.07*Math.sin(ph)*w*(k+1)/3;pose.s[k*3+2]=0;}
 pose.n[0]=-.1*w;pose.n[1]=0;pose.n[2]=0;pose.hd[0]=-L[1]*.65-.3*w;pose.hd[1]=0;pose.hd[2]=0;
 for(let i=0;i<2;i++){const sd=i?1:-1,sw=Math.sin(ph+(i?0:Math.PI)),q=pose.a[i];   // arms reach up, opposite to the legs
  q[0]=mnLerp(rest,-2.45+.6*sw+1.5*mu,w);q[1]=0;q[2]=sd*mnLerp(P.armOut,.3,w);q[3]=mnLerp(-.25,-.55+.3*sw,w);q[4]=-.25;}
 for(let i=0;i<2;i++){const f=pose.f[i],T=A.foot[i];f[0]=T.x;f[1]=T.y;f[2]=T.z;f[3]=A.zN[i+2];f[4]=0;}
 mnApplyPose(m,pose);
}
function tryMonsterClimb(m,tx,tz,ty){
 if(m.climb||m.roof||m.entry||m.down)return false;
 let c=null;for(const q of colliders){if(q.kind!=='building'||q.top<3)continue;if(insideXZ(q,tx,tz,1.2)&&(!c||q.top>c.top))c=q;}
 if(!c||ty<c.top-2.5)return false;   // the target is not standing on a building
 const p=m.root.position,cx=THREE.MathUtils.clamp(p.x,c.x-c.halfX,c.x+c.halfX),cz=THREE.MathUtils.clamp(p.z,c.z-c.halfZ,c.z+c.halfZ);
 let nx=p.x-cx,nz=p.z-cz;const l=Math.hypot(nx,nz);if(l<1e-3||l>m.cfg.scale*1.6+2.5)return false;   // must already be at the wall
 m.climb={phase:'approach',c,nx:nx/l,nz:nz/l,cx,cz,t:0,ph:0,t2:0};m.anim.cw=0;m.anim.leap=null;return true;
}
function monsterClimbStep(m,dt){
 const k=m.climb,A=m.anim,p=m.root.position,sc=m.cfg.scale,c=k.c,rad=.5*sc+.2;k.t+=dt;
 if(k.t>14||!m.alive){m.climb=null;return;}
 {const onB=insideXZ(c,player.pos.x,player.pos.z,3)&&player.pos.y>c.top-3;k.off=onB?0:(k.off||0)+dt;
  if(k.off>.35){m.climb=null;A.cw=0;A.leap=null;m.detour=null;m.path=null;return;}}   // the player came down: give up the climb and drop back to the ground
 const fy=Math.atan2(-k.nx,-k.nz);A.yaw+=mnWrap(fy-A.yaw)*(1-Math.exp(-14*dt));m.root.rotation.y=A.yaw;
 if(k.phase==='approach'){
  const sx=k.cx+k.nx*rad,sz=k.cz+k.nz*rad,dx=sx-p.x,dz=sz-p.z,d=Math.hypot(dx,dz),st=Math.min(d,m.cfg.speed*dt*1.2);
  if(d>.08){p.x+=dx/d*st;p.z+=dz/d*st;mnAnimate(m,dt);}else{k.phase='wall';k.y0=p.y;}
  return;}
 if(k.phase==='wall'){
  const sp=CLIMB.speed*(m.type==='stalker'?1.3:m.type==='brute'?.8:1);
  p.y+=sp*dt;k.ph+=dt*sp/1.6*Math.PI*2;p.x=k.cx+k.nx*rad;p.z=k.cz+k.nz*rad;
  mnClimbApply(m,dt,k.ph,0);
  if(p.y>=c.top-.9){k.phase='mantle';k.t2=0;k.y1=p.y;}
  return;}
 k.t2+=dt;const u=Math.min(1,k.t2/.55),e=mnSmooth(u);   // mantle: pull up and over the edge onto the roof
 p.y=k.y1+(c.top+.05-k.y1)*e;p.x=k.cx+k.nx*(rad-(rad+.9)*e);p.z=k.cz+k.nz*(rad-(rad+.9)*e);
 k.ph+=dt*9;mnClimbApply(m,dt,k.ph,u);
 if(u>=1){m.climb=null;m.roof={c,off:0};A.lastX=p.x;A.lastZ=p.z;A.leap=null;A.cw=0;}
}
function moveMonsterRoof(m,tx,tz,dt,tw){
 const R=m.roof,c=R.c,p=m.root.position,dx=tx-p.x,dz=tz-p.z,dist=Math.hypot(dx,dz);
 const onTarget=!tw&&insideXZ(c,tx,tz,3)&&player.pos.y>c.top-3;
 R.off=onTarget?0:R.off+dt;
 if(R.off>.6){   // the target left the building: leap off toward it
  const g=WALL_ENTRY.gravity,gy=m.spawn.y,l=dist||1,ux=dx/l,uz=dz/l;let lx=p.x+ux*8,lz=p.z+uz*8;
  for(let d=6;d<34;d+=2){const x=p.x+ux*d,z=p.z+uz*d;if(!insideXZ(c,x,z,1.5)&&monsterSpotFree(x,z,1.4*m.cfg.scale)){lx=x;lz=z;break;}}
  const T=Math.sqrt(2*Math.max(0,p.y-gy)/g)+.45;
  m.roof=null;m.entry={phase:'crouch',a:0,t:0,c:0,T,vel:new THREE.Vector3((lx-p.x)/T,(gy-p.y+.5*g*T*T)/T,(lz-p.z)/T)};m.anim.leap=null;return false;}
 const step=Math.min(m.cfg.speed*dt,Math.max(0,dist-m.cfg.range*.78));let moved=false;
 if(step>.001){p.x=THREE.MathUtils.clamp(p.x+dx/dist*step,c.x-c.halfX+.4,c.x+c.halfX-.4);p.z=THREE.MathUtils.clamp(p.z+dz/dist*step,c.z-c.halfZ+.4,c.z+c.halfZ-.4);moved=true;}
 const ry=roofSurfaceAt(p.x,p.z),ty=Math.max(c.top+.05,ry===null?0:ry);p.y+=(ty-p.y)*(1-Math.exp(-14*dt));
 return moved;
}
function moveMonsterAuto(m,tx,tz,dt,tw){
 if(m.roof)return moveMonsterRoof(m,tx,tz,dt,tw);
 if(!tw&&player.pos.y>m.root.position.y+CLIMB.minDy&&tryMonsterClimb(m,tx,tz,player.pos.y))return false;
 return moveMonsterToward(m,tx,tz,dt);
}

// ---- Peasant Girl model as the captive: arms tied behind her, then animated on top of that pose (breathing, struggling, flinching, slumping)
const _cq1=new THREE.Quaternion(),_cq2=new THREE.Quaternion(),_cq3=new THREE.Quaternion(),_cX=new THREE.Vector3(1,0,0),_cY=new THREE.Vector3(0,1,0),_cZ=new THREE.Vector3(0,0,1);
function captiveRotW(bone,axis,ang){if(!bone||!ang)return;bone.updateWorldMatrix(true,false);const wq=bone.getWorldQuaternion(_cq1),pq=bone.parent.getWorldQuaternion(_cq2);wq.premultiply(_cq3.setFromAxisAngle(axis,ang));bone.quaternion.copy(pq.invert().multiply(wq));bone.updateMatrixWorld(true);}
function captiveModelAnim(dt){
 const C=CAPTIVE,Mo=C.model,t=C.t,hp=C.hp/C.max,B=Mo.B;
 C.sl+=((C.alive?0:1)-C.sl)*(1-Math.exp(-3*dt));
 for(const [b,q] of Mo.base)b.quaternion.copy(q);
 const live=C.alive?1:0,fear=C.flinch+(1-hp)*.5+C.under*.5,sb=Math.pow(Math.max(0,Math.sin(t*.9)),6)*(.4+fear)*live,sl=C.sl;
 captiveRotW(B.hips,_cZ,.05*sb*Math.sin(t*14));
 captiveRotW(B.spine1,_cX,.1*(1-hp)*live+.45*sl+.02*Math.sin(t*1.7));
 captiveRotW(B.spine2,_cX,.015*Math.sin(t*2.1));
 captiveRotW(B.head,_cX,.1+.04*Math.sin(t*1.3)+.45*C.flinch+1*sl);
 captiveRotW(B.head,_cY,(.35*Math.sin(t*.6)+.25*sb*Math.sin(t*19))*(1-sl));
 captiveRotW(B.leftarm,_cX,.1*sb*Math.sin(t*15));captiveRotW(B.rightarm,_cX,.1*sb*Math.sin(t*15+1.7));
}
async function loadCaptiveModel(M,loaderModule){
 const node=document.getElementById('captiveModel'),C=CAPTIVE;if(!node||!C.group)return;
 const loader=new loaderModule.FBXLoader(),model=loader.parse(erikaB64(node.textContent.trim()),'');node.remove();
 model.position.set(0,0,0);model.quaternion.identity();model.scale.set(1,1,1);model.updateMatrixWorld(true);
 const box=new M.Box3().setFromObject(model),k=1.68/Math.max(.01,box.max.y-box.min.y);
 model.scale.setScalar(k);model.position.y=-box.min.y*k;
 const holder=new M.Group();holder.position.set(0,.16,.3);holder.add(model);C.group.add(holder);
 const B={};model.traverse(o=>{if(o.isBone){const n=mnBoneKey(o);if(!B[n])B[n]=o;}});
 const wp=o=>o.getWorldPosition(new M.Vector3());
 C.group.updateMatrixWorld(true);
 if(B.lefttoebase&&B.leftfoot&&wp(B.lefttoebase).z-wp(B.leftfoot).z<0){holder.rotation.y=Math.PI;C.group.updateMatrixWorld(true);}   // make sure she faces away from the post
 const sL=Math.sign(wp(B.leftarm).x-wp(B.hips).x)||1;
 const aim=(bone,child,dir)=>{if(!bone||!child)return;bone.updateWorldMatrix(true,true);const cur=wp(child).sub(wp(bone)).normalize(),q=new M.Quaternion().setFromUnitVectors(cur,dir.clone().normalize()),wq=bone.getWorldQuaternion(new M.Quaternion()),pq=bone.parent.getWorldQuaternion(new M.Quaternion());wq.premultiply(q);bone.quaternion.copy(pq.invert().multiply(wq));bone.updateMatrixWorld(true);};
 const V=(x,y,z)=>new M.Vector3(x,y,z);
 aim(B.leftarm,B.leftforearm,V(.18*sL,-1,-.3));aim(B.leftforearm,B.lefthand,V(-.25*sL,-.55,-.8));      // hands tied behind her back
 aim(B.rightarm,B.rightforearm,V(-.18*sL,-1,-.3));aim(B.rightforearm,B.righthand,V(.25*sL,-.55,-.8));
 model.traverse(o=>{if(o.isMesh){o.castShadow=false;o.receiveShadow=false;o.frustumCulled=false;}});
 const keys=['hips','spine','spine1','spine2','neck','head','leftarm','rightarm','leftforearm','rightforearm'];
 C.model={B,base:keys.filter(n=>B[n]).map(n=>[B[n],B[n].quaternion.clone()])};C.sl=0;
 if(C.P.W){C.group.remove(C.P.W);C.P={};}   // the procedural woman is gone
}
function respawnMonster(m){
 m.alive=true;m.dead=false;m.hp=m.maxHp;m.deadTimer=0;m.attackCooldown=.8;m.recoil=0;m.lastSwordSerial=0;m.attackSerial=0;m.lieTT=undefined;m.down=null;m.rd=null;
 m.root.visible=true;m.rig.visible=true;if(m.model)m.model.visible=true;m.farHidden=false;m.root.position.copy(m.spawn);m.root.rotation.set(0,0,0);m.root.scale.setScalar(m.cfg.scale);
 mnInit(m);for(const mesh of m.hitMeshes)monsterHitMeshes.push(mesh);startWallEntry(m,0);m.root.updateMatrixWorld(true);
}
// ===================== WAVES: wave 1 = a few monsters, every next wave is bigger =====================
// Tweak: WAVES.first (monsters in wave 1), WAVES.step (extra monsters per wave), WAVES.pause (seconds of rest between waves), HORDE.cap (max alive at once)
const WAVES={n:1,state:'fight',maxSpitters:9,first:6,step:3,pause:10,breakT:0,toSpawn:0,left:0,spawnT:0,lt:0};
function waveCount(n){return Math.min(HORDE.cap,WAVES.first+(n-1)*WAVES.step);}
function waveSpawnOne(){
 let spare=null;for(const m of monsters){if(m.dead&&!m.alive&&!m.root.visible&&!m.boss){spare=m;break;}}
 let m=spare;
 if(m)respawnMonster(m);
 else if(monsters.length<HORDE.cap+8){const r=Math.random(),nSp=monsters.reduce((a,x)=>a+(x.type==='spitter'?1:0),0),ty=nSp>=WAVES.maxSpitters?(r<.4?'brute':'stalker'):(r<.3?'brute':r<.75?'stalker':'spitter');m=createMonster(ty,0,0);const W=globalThis.MN_SWAP,pr=W&&W.protos[m.type];if(pr)try{mnSwapToModel(W.M,W.SU,m,pr);}catch(err){console.warn('Monster model swap failed:',err);}startWallEntry(m,0);}
 else return false;
 balApplyHp(m);if(m.entry)m.entry.t=Math.random()*1.2;
 return true;
}
function hordeUpdate(dt){
 if(monsterRespawnTimer>0||!monsters.length)return;HORDE.t+=dt;
 let alive=0;for(const m of monsters)if(m.alive)alive++;if(BOSS.want)alive++;   // a boss that is about to appear keeps the wave open
 
 WAVES.left=alive+WAVES.toSpawn;
 if(WAVES.state==='break'){
  if(!UPG.open)WAVES.breakT-=dt;   // the countdown freezes while the upgrade menu is open
  if(WAVES.breakT<=0){WAVES.n++;WAVES.toSpawn=waveCount(WAVES.n);WAVES.state='fight';WAVES.spawnT=0;try{showToast('WAVE '+WAVES.n+' - '+WAVES.toSpawn+' MONSTERS');}catch(e){}}
  return;
 }
 if(WAVES.toSpawn>0){
  WAVES.spawnT-=dt;
  if(WAVES.spawnT<=0){if(waveSpawnOne()){WAVES.toSpawn--;WAVES.spawnT=.45;}else WAVES.spawnT=1;}
  return;
 }
 if(alive===0){WAVES.state='break';WAVES.breakT=WAVES.pause;AMMO.max=AMMO.start+AMMO.perWave*WAVES.n;AMMO.cur=AMMO.max;
  if(!playerDeath.active){if(playerHealth<UP.maxHp)playerHealth=Math.min(UP.maxHp,playerHealth+50);const C=CAPTIVE;if(C.alive&&C.hp<C.max){C.hp=Math.min(C.max,C.hp+180);captiveSetBar();}updateMonsterHUD();}   // wave reward: +50 health for you (max 100), +180 for the captive (max 600)
  try{xpWaveCheck();}catch(e){console.warn(e);}
  try{showToast('WAVE '+WAVES.n+' CLEARED - NEXT WAVE IS BIGGER - ARROWS: '+AMMO.max);}catch(e){}}
}
function resetMonsters(){
 bossReset();
 for(const m of monsters){m.maxHp=m.cfg.hp;m.hp=m.maxHp;}
 for(const p of monsterProjectiles)scene?.remove(p.mesh);monsterProjectiles.length=0;monsterKills=0;AMMO.max=AMMO.start;AMMO.cur=AMMO.max;
 monsterHitMeshes.length=0;HORDE.t=0;HORDE.spawnT=3;HORDE.start=WAVES.first;WAVES.n=1;WAVES.state='fight';WAVES.toSpawn=0;WAVES.breakT=0;WAVES.left=WAVES.first;for(const m of monsters){if(monsters.indexOf(m)>=HORDE.start){m.alive=false;m.dead=true;m.entry=null;m.root.visible=false;continue;}m.alive=true;m.dead=false;m.hp=m.maxHp;m.deadTimer=0;m.attackCooldown=.8;m.recoil=0;m.lastSwordSerial=0;m.attackSerial=0;m.lieTT=undefined;m.down=null;m.rd=null;m.root.visible=true;m.root.position.copy(m.spawn);m.root.rotation.set(0,0,0);m.root.scale.setScalar(m.cfg.scale);
  mnInit(m);startWallEntry(m,monsters.indexOf(m));for(const mesh of m.hitMeshes)monsterHitMeshes.push(mesh);m.root.updateMatrixWorld(true);}
 updateMonsterHUD();
}
// Forgiving hit box: a vertical capsule around each monster tested against the arrow's path this frame (segment-segment closest point),
// so a fast arrow can no longer slip between the monster's triangles. Tweak: ARROW_HIT.r (radius per unit of monster scale) / .pad (metres)
const ARROW_HIT={r:.55,pad:.18,y0:.1,y1:2.0};
function arrowCapsuleHit(O,dir,L){
 let best=null;if(!(L>1e-5))return null;
 const Dx=dir.x*L,Dy=dir.y*L,Dz=dir.z*L,a=L*L;
 for(const m of monsters){
  if(!m.alive||m.entry||!m.root.visible)continue;
  const p=m.root.position,sc=m.cfg.scale,R=ARROW_HIT.r*sc+ARROW_HIT.pad,Bx=p.x,By=p.y+ARROW_HIT.y0*sc,Bz=p.z,h=(ARROW_HIT.y1-ARROW_HIT.y0)*sc;
  const rx=O.x-Bx,ry=O.y-By,rz=O.z-Bz;
  const e=h*h,f=h*ry,c=Dx*rx+Dy*ry+Dz*rz,b=Dy*h,den=a*e-b*b;
  let sp=den>1e-9?(b*f-c*e)/den:0;sp=sp<0?0:sp>1?1:sp;
  let t=(b*sp+f)/e;
  if(t<0){t=0;sp=-c/a;sp=sp<0?0:sp>1?1:sp;}else if(t>1){t=1;sp=(b-c)/a;sp=sp<0?0:sp>1?1:sp;}
  const px=O.x+Dx*sp,py=O.y+Dy*sp,pz=O.z+Dz*sp,qx=Bx,qy=By+h*t,qz=Bz,d2=(px-qx)**2+(py-qy)**2+(pz-qz)**2;
  if(d2>R*R)continue;
  const se=Math.max(0,sp-Math.sqrt(R*R-d2)/L),dist=se*L;   // entry point of the capsule
  if(!best||dist<best.distance)best={m,distance:dist,point:new THREE.Vector3(O.x+Dx*se,O.y+Dy*se,O.z+Dz*se)};
 }
 return best;
}
function updateArrows(dt){
 if(!(dt>0))return;
 for(let i=bow.arrows.length-1;i>=0;i--){
  const a=bow.arrows[i];
  if(a.state==='fly'){
   a.vel.y-=BOW.gravity*dt;
   const dist=a.vel.length()*dt;
   if(dist>1e-5){
    _arrowDir.copy(a.vel).normalize();
    raycaster.set(a.pos,_arrowDir);raycaster.near=0;raycaster.far=dist+.3;
    const hits=raycaster.intersectObjects(grappleTargetMeshes,false),monsterHits=monsterHitMeshes.length?raycaster.intersectObjects(monsterRayCandidates(a.pos,dist+9),false):[];let monsterHit=null;
    for(const mh of monsterHits){if(mh.object.userData.monster&&mh.object.userData.monster.alive){monsterHit=mh;break;}}
    {const ch=arrowCapsuleHit(a.pos,_arrowDir,dist+.3);if(ch&&(!monsterHit||ch.distance<monsterHit.distance))monsterHit={object:{userData:{monster:ch.m}},distance:ch.distance,point:ch.point};}
    const worldHit=hits[0];
    if(monsterHit&&(!worldHit||monsterHit.distance<worldHit.distance)){
     {const hm=monsterHit.object.userData.monster,wasAlive=hm.alive;if(hm.boss)BOSS.hitPt=monsterHit.point;else MNUM.pt=monsterHit.point;damageMonster(hm,BAL.arrowBase+Math.round((a.power||.2)*BAL.arrowPow),'arrow');arrowHitMonsterFx(monsterHit.point,_arrowDir,hm,wasAlive&&!hm.alive);}a.monster=monsterHit.object.userData.monster;a.pos.copy(monsterHit.point).addScaledVector(_arrowDir,.14);
     a.state='stuck';a.life=BOW.stuckTime;a.trailFade=1;a.vel.set(0,0,0);a.mesh.userData.trail.visible=false;sound('arrowhit');
    }else if(worldHit){
     arrowHitWallFx(worldHit.point,_arrowDir);a.pos.copy(worldHit.point).addScaledVector(_arrowDir,.14);
     a.state='stuck';a.life=BOW.stuckTime;a.trailFade=1;a.vel.set(0,0,0);a.mesh.userData.trail.visible=false;sound('arrowhit');
    }else{const f0=_afx.u.copy(a.pos);a.pos.addScaledVector(_arrowDir,dist);arrowTrailFx(a,f0,a.pos,dt);}
    a.mesh.quaternion.setFromUnitVectors(_arrowFwd,_arrowDir);
   }
   a.mesh.position.copy(a.pos);updateArrowPathTrail(a);
   if(a.state==='fly'&&(a.pos.y<-40||a.pos.lengthSq()>900*900)){disposeArrow(a);bow.arrows.splice(i,1);continue;}
  }else{
   if(a.monster&&!a.monster.alive){disposeArrow(a);bow.arrows.splice(i,1);continue;}   // arrow stuck in a monster vanishes with its death
   if(a.monster){const r=a.monster.root;r.updateWorldMatrix(true,false);   // stuck in a monster: follow its body
    if(!a.att){a.attP=r.worldToLocal(a.mesh.position.clone());a.attQ=r.getWorldQuaternion(new THREE.Quaternion()).invert().multiply(a.mesh.quaternion);a.att=true;}
    else{a.mesh.position.copy(r.localToWorld(a.attP.clone()));a.mesh.quaternion.copy(r.getWorldQuaternion(new THREE.Quaternion()).multiply(a.attQ));}}
   a.life-=dt;
   if(a.trail&&a.trailFade>0){a.trailFade=Math.max(0,a.trailFade-dt);a.trail.line.material.opacity=a.trail.opacity*a.trailFade;if(a.trailFade===0)a.trail.line.visible=false;}
   if(a.life<1.5)a.mesh.scale.setScalar(Math.max(.001,1.5*(a.life/1.5)));
   if(a.life<=0){disposeArrow(a);bow.arrows.splice(i,1);}
  }
 }
}
// ===================== FIRST-PERSON BODY MASK =====================
// First person shows ONLY: both arms/hands while aiming the bow, and both legs while running. Everything else
// (torso, head, hair, clothes) is discarded per-pixel from per-vertex skin weights, so looking down never shows the body's inside.
const erikaFP={uFP:{value:0},uLegs:{value:0},uArms:{value:0},uArmR:{value:0},uArmL:{value:0}};
function setupErikaFPMask(model){
 const M=erikaModule||THREE;
 model.traverse(mesh=>{
  if(!mesh.isSkinnedMesh||!mesh.skeleton||!mesh.geometry)return;
  const isClothesMesh=erikaNormName(mesh.name).includes('clothes');
  if(isClothesMesh)mesh.userData.erikaClothesMesh=true;
  const geo=mesh.geometry,si=geo.getAttribute('skinIndex'),sw=geo.getAttribute('skinWeight'),pos=geo.getAttribute('position');
  if(!si||!sw||!pos)return;
  const legB=new Set(),armB=new Set(),armR=new Set();
  mesh.skeleton.bones.forEach((bone,i)=>{const n=erikaNormName(bone.name);
   if(n.includes('upleg')||n.endsWith('leg')||n.includes('foot')||n.includes('toe'))legB.add(i);
   else if(n.includes('arm')||n.includes('hand')){armB.add(i);if(n.includes('right'))armR.add(i);}});
  const a=new Float32Array(pos.count*3);
  for(let i=0;i<pos.count;i++){let l=0,r=0,rr=0;for(let j=0;j<4;j++){const b=si.getComponent(i,j),w=sw.getComponent(i,j);if(legB.has(b))l+=w;else if(armB.has(b)){r+=w;if(armR.has(b))rr+=w;}}a[i*3]=l;a[i*3+1]=r;a[i*3+2]=rr;}
  geo.setAttribute('aFP',new M.BufferAttribute(a,3));
  const sourceList=Array.isArray(mesh.material)?mesh.material:[mesh.material];
  const list=sourceList.map(mt=>mt?mt.clone():mt);
  mesh.material=Array.isArray(mesh.material)?list:list[0];
  for(const mt of list){
   if(!mt)continue;mt.userData.erikaFP=true;
   const prev=mt.onBeforeCompile;
   mt.onBeforeCompile=(shader,rend)=>{
    if(prev)prev.call(mt,shader,rend);
    shader.uniforms.uFPClothes={value:isClothesMesh?-1:1};
    shader.uniforms.uFP=erikaFP.uFP;shader.uniforms.uLegs=erikaFP.uLegs;shader.uniforms.uArms=erikaFP.uArms;shader.uniforms.uArmR=erikaFP.uArmR;shader.uniforms.uArmL=erikaFP.uArmL;
    shader.vertexShader=shader.vertexShader.replace('#include <common>','#include <common>\nattribute vec3 aFP;\nvarying vec3 vFP;').replace('#include <begin_vertex>','#include <begin_vertex>\nvFP=aFP;');
    shader.fragmentShader=shader.fragmentShader.replace('#include <common>','#include <common>\nvarying vec3 vFP;\nuniform float uFP;\nuniform float uFPClothes;\nuniform float uLegs;\nuniform float uArms;\nuniform float uArmR;\nuniform float uArmL;').replace('void main() {','void main() {\n if(uFP>.5){if(uFPClothes<.5)discard;bool keep=(uLegs>.5&&vFP.x>.05)||(uArms>.5&&vFP.y>.05)||(uArmR>.5&&vFP.z>.05)||(uArmL>.5&&vFP.y>.05&&vFP.z<.05);if(!keep)discard;}\n');
   };
   mt.customProgramCacheKey=()=>`erikaFPmask4-${isClothesMesh?'clothes':'body'}`;
   mt.needsUpdate=true;
  }
 });
}
function updateErikaFPMask(){
 erikaFP.uFP.value=thirdPerson?0:1;
 erikaFP.uLegs.value=(player.grounded&&(player.sliding||player.moveSpeed>.65))?1:0;
 const walkingWhileAimingBow=weapon==='bow'&&(bow.aiming||bow.drawing)&&player.grounded&&!player.sliding&&player.moveSpeed>.65;
 erikaFP.uArms.value=(weapon==='sword'||sword.hold>.02||(!walkingWhileAimingBow&&(bow.drawing||bow.equip>.02||(player.grounded&&!player.sliding&&player.moveSpeed>.65))))?1:0;
 erikaFP.uArmR.value=(weapon==='sword'||sword.hold>.02)?1:0;
 erikaFP.uArmL.value=((weapon==='bow'||sword.lhold>.02)&&!walkingWhileAimingBow)?1:0;
 if(erikaPlayer&&erikaPlayer.root)erikaPlayer.root.traverse(mesh=>{
  if(mesh.userData&&mesh.userData.erikaClothesMesh)mesh.visible=thirdPerson;
 });
}
// ===================== HIP GRAPPLE LAUNCHERS =====================
const hipLaunchers=[];const _hipQ=new THREE.Quaternion(),_hipOff=new THREE.Vector3(),_hipAim=new THREE.Object3D(),_hipTv=new THREE.Vector3();
function createHipLaunchers(){
 if(hipLaunchers.length)return;
 for(const d of grappleDevices)if(d.group)d.group.visible=false;
 for(const side of [-1,1]){
  const g=new THREE.Group();g.name=(side<0?'Left':'Right')+'HipGrappleLauncher';
  const shell=new THREE.Mesh(new THREE.BoxGeometry(.11,.1,.16),mats.metal);shell.position.set(0,0,.02);g.add(shell);
  const plate=new THREE.Mesh(new THREE.BoxGeometry(.13,.035,.12),mats.ninjaAccent||mats.metal);plate.position.set(0,.065,.03);g.add(plate);
  const barrel=new THREE.Mesh(new THREE.CylinderGeometry(.022,.028,.14,8),mats.metal);barrel.rotation.x=Math.PI/2;barrel.position.set(0,0,-.1);g.add(barrel);
  g.traverse(o=>{o.castShadow=false;o.receiveShadow=false;});
  scene.add(g);hipLaunchers.push({side,group:g});
 }
}
function updateHipLaunchers(){
 if(!playerMesh||!hipLaunchers.length)return;
 for(const L of hipLaunchers){
  L.group.visible=thirdPerson;
  const h=hooks[L.side<0?0:1],p=getHandWorld(L.side);
  L.group.position.copy(p);
  const t=h.mode==='attached'&&h.anchor?h.anchor:(h.mode==='flying'&&h.tip?h.tip.position:null);
  if(t){_hipAim.position.copy(p);_hipTv.copy(p).multiplyScalar(2).sub(t);_hipAim.lookAt(_hipTv);L.group.quaternion.copy(_hipAim.quaternion);}
  else{const hips=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.hips;if(hips){hips.getWorldQuaternion(L.group.quaternion);if(erikaPlayer.hipRootRotation)L.group.quaternion.multiply(erikaPlayer.hipRootRotation);}else playerMesh.getWorldQuaternion(L.group.quaternion);}
 }
}

const v3=(x=0,y=0,z=0)=>new THREE.Vector3(x,y,z);
function mat(color,roughness=.8,metalness=0){return new THREE.MeshStandardMaterial({color,roughness,metalness});}
function canvasTexture(kind){const c=document.createElement('canvas');c.width=256;c.height=256;const x=c.getContext('2d');
 if(kind==='stone'){x.fillStyle='#77766d';x.fillRect(0,0,256,256);for(let y=0;y<256;y+=32){let off=((y/32)%2)*18;for(let xx=-off;xx<256;xx+=55){x.fillStyle=['#85847a','#73736c','#8d897d','#666760'][Math.floor(Math.random()*4)];x.fillRect(xx+2,y+2,51,28);x.strokeStyle='#4b4d4a';x.lineWidth=2;x.strokeRect(xx+2,y+2,51,28);}}for(let i=0;i<4000;i++){x.fillStyle=Math.random()>.5?'rgba(255,255,255,.035)':'rgba(0,0,0,.045)';x.fillRect(Math.random()*256,Math.random()*256,2,2);}}
 if(kind==='plaster'){x.fillStyle='#c1ad8d';x.fillRect(0,0,256,256);for(let i=0;i<1600;i++){x.fillStyle=Math.random()>.5?'rgba(78,60,39,.05)':'rgba(255,255,255,.06)';x.fillRect(Math.random()*256,Math.random()*256,4+Math.random()*10,2+Math.random()*6);}x.strokeStyle='rgba(75,57,38,.2)';for(let y=32;y<256;y+=64){x.beginPath();x.moveTo(0,y);x.lineTo(256,y);x.stroke();}}
 if(kind==='roof'){x.fillStyle='#614139';x.fillRect(0,0,256,256);for(let y=0;y<256;y+=17){for(let xx=-12;xx<256;xx+=28){let xx2=xx+((y/17)%2)*14;x.fillStyle=['#774d3c','#8a5d45','#6c4339','#956749'][Math.floor(Math.random()*4)];x.fillRect(xx2+1,y+1,26,15);x.strokeStyle='#3c2d2a';x.lineWidth=1.5;x.strokeRect(xx2+1,y+1,26,15);x.beginPath();x.moveTo(xx2+2,y+3);x.lineTo(xx2+24,y+3);x.strokeStyle='rgba(226,177,123,.23)';x.stroke();}}}
 if(kind==='grass'){x.fillStyle='#6d7a4c';x.fillRect(0,0,256,256);for(let i=0;i<46;i++){const px=Math.random()*256,py=Math.random()*256,pr=14+Math.random()*34,cc=['98,120,66','126,112,70','84,106,62','112,98,66'][i%4];for(const ox of [-256,0,256])for(const oy of [-256,0,256]){const gx=px+ox,gy=py+oy;if(gx+pr<0||gx-pr>256||gy+pr<0||gy-pr>256)continue;const g=x.createRadialGradient(gx,gy,2,gx,gy,pr);g.addColorStop(0,'rgba('+cc+',.55)');g.addColorStop(1,'rgba('+cc+',0)');x.fillStyle=g;x.fillRect(gx-pr,gy-pr,pr*2,pr*2);}}for(let i=0;i<2600;i++){x.strokeStyle=['rgba(52,74,38,.38)','rgba(140,150,84,.30)','rgba(96,84,52,.25)'][i%3];x.lineWidth=1;const px=Math.random()*256,py=Math.random()*256;x.beginPath();x.moveTo(px,py);x.lineTo(px+(Math.random()-.5)*3,py-2-Math.random()*5);x.stroke();}for(let i=0;i<40;i++){x.fillStyle='rgba(120,112,98,.5)';x.beginPath();x.arc(Math.random()*256,Math.random()*256,1+Math.random()*2,0,6.283);x.fill();}}
 if(kind==='cobble'){x.fillStyle='#4f4d47';x.fillRect(0,0,256,256);const sh=['#a8a392','#9a9486','#b0aa99','#8e8a7d','#a09a8a','#b8b2a2'],N=7,sw=256/N,pick=[];for(let r=0;r<8;r++){pick.push([]);for(let i=0;i<N;i++)pick[r].push(Math.floor(Math.random()*6));}for(let r=0;r<8;r++){const y0=r*32,off=(r%2)*sw/2;for(let i=-1;i<=N;i++){const px=i*sw-off+2,py=y0+2,pw=sw-4,ph=28,rr=6;x.fillStyle=sh[pick[r][(i+N)%N]];x.beginPath();x.moveTo(px+rr,py);x.arcTo(px+pw,py,px+pw,py+ph,rr);x.arcTo(px+pw,py+ph,px,py+ph,rr);x.arcTo(px,py+ph,px,py,rr);x.arcTo(px,py,px+pw,py,rr);x.closePath();x.fill();x.fillStyle='rgba(255,255,255,.12)';x.fillRect(px+4,py+2,pw-10,3);x.fillStyle='rgba(0,0,0,.14)';x.fillRect(px+4,py+ph-5,pw-8,3);}}for(let i=0;i<1100;i++){x.fillStyle=Math.random()>.5?'rgba(255,255,255,.05)':'rgba(0,0,0,.07)';x.fillRect(Math.random()*256,Math.random()*256,2,2);}for(let i=0;i<50;i++){x.fillStyle='rgba(88,112,62,.32)';x.beginPath();x.arc(Math.random()*256,Math.random()*256,1+Math.random()*3,0,6.283);x.fill();}}
 const t=new THREE.CanvasTexture(c);t.wrapS=t.wrapT=THREE.RepeatWrapping;t.colorSpace=THREE.SRGBColorSpace;t.anisotropy=4;return t;}
let texStone,texPlaster,texRoof;
const mats={};
function boxMesh(w,h,d,material,x,y,z,parent=worldRoot,rotY=0){const m=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),material);m.position.set(x,y,z);m.rotation.y=rotY;m.castShadow=true;m.receiveShadow=true;parent.add(m);staticBoxCandidates.push(m);return m;}
function addCollider(x,z,w,d,top,kind='building'){colliders.push({x,z,halfX:w/2,halfZ:d/2,top,kind});}
// The triangular gable end is a solid prism but had no collider above the wall top, so the player could walk into it.
// Approximate it with a stack of narrowing boxes (bottom = wall top, top below the roof plane); each only blocks horizontally.
function addGableColliders(x,z,w,roofD,h,roofRise){
 const N=7,y0=.6,span=roofRise-.75;
 for(let i=0;i<N;i++){const top=h+y0+i*span/(N-1),halfX=Math.max(.1,(w*.5-.08)*(1-(top-h)/roofRise));
  colliders.push({x,z,halfX,halfZ:roofD/2-.22,top,bottom:h+.15,kind:'gable'});}
}
function addRoofSurface(x,z,halfX,halfZ,centerY,slope=0){roofSurfaces.push({x,z,halfX,halfZ,centerY,slope});}
function roofSurfaceAt(x,z){let highest=null;for(const s of roofSurfaces){if(Math.abs(x-s.x)>s.halfX+.2||Math.abs(z-s.z)>s.halfZ+.2)continue;const y=s.centerY+(x-s.x)*s.slope;if(highest===null||y>highest)highest=y;}return highest;}
function addSolid(m,target=true){solidMeshes.push(m);if(target)targetMeshes.push(m);return m;}
function orientedBox(w,h,d,material,position,rotationY=0,parent=worldRoot){const m=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),material);m.position.copy(position);m.rotation.y=rotationY;m.castShadow=true;m.receiveShadow=true;parent.add(m);return m;}
// Small rooftop obstacles use the same collision system as the rest of the city.
function addRoofBox(w,h,d,material,x,y,z,kind='prop'){
 const m=boxMesh(w,h,d,material,x,y,z);
 colliders.push({x,z,halfX:w/2,halfZ:d/2,bottom:y-h/2,top:y+h/2,kind});
 return m;
}
function addRoofCylinder(x,y,z,r,h,material,sides=12){
 const m=new THREE.Mesh(new THREE.CylinderGeometry(r*.92,r,h,sides),material);
 m.position.set(x,y,z);m.castShadow=true;m.receiveShadow=true;worldRoot.add(m);
 colliders.push({x,z,halfX:r*.9,halfZ:r*.9,bottom:y-h/2,top:y+h/2,kind:'prop'});
 return m;
}
function buildOpenRooftop(x,z,w,d,h,variant,roofMat){
 const deckY=h+.29,deckW=w+.12,deckD=d+.12;
 const deck=boxMesh(deckW,.34,deckD,mats.roofDeck,x,h+.12,z);tileBoxUV(deck.geometry,deckW,.34,deckD,4);addSolid(deck,true);
 addCollider(x,z,w,d,deckY,'roof');addRoofSurface(x,z,w/2-.18,d/2-.18,deckY,0);
 // Low perimeter parapets: the roof remains completely uncovered and its centre stays clear for parkour.
 const ph=.82+(variant%3)*.08,pt=.42,edge=mats.roofEdge;
 if(variant%3===2){
  // Open metal guardrails on a few terraces instead of solid parapet walls.
  for(const side of [-1,1]){
   const zz=z+side*(d/2-.22);addRoofBox(w-.65,.16,.14,mats.darkWood,x,deckY+1.02,zz);
   addRoofBox(w-.65,.13,.12,mats.metal,x,deckY+.48,zz);
   for(let q=-2;q<=2;q++)addRoofBox(.12,1.02,.12,mats.metal,x+q*(w-.9)/4,deckY+.51,zz);
  }
  for(const side of [-1,1]){
   const xx=x+side*(w/2-.22);addRoofBox(.14,.16,d-.65,mats.darkWood,xx,deckY+1.02,z);
   addRoofBox(.12,.13,d-.65,mats.metal,xx,deckY+.48,z);
   for(let q=-2;q<=2;q++)addRoofBox(.12,1.02,.12,mats.metal,xx,deckY+.51,z+q*(d-.9)/4);
  }
 }else{
  addRoofBox(w-.65,ph,pt,edge,x,deckY+ph/2,z-d/2+.22);
  addRoofBox(w-.65,ph,pt,edge,x,deckY+ph/2,z+d/2-.22);
  addRoofBox(pt,ph,d-.65,edge,x-w/2+.22,deckY+ph/2,z);
  addRoofBox(pt,ph,d-.65,edge,x+w/2-.22,deckY+ph/2,z);
 }
 // Stone coping and corner pillars give the roof a finished architectural edge.
 for(const sx of [-1,1])for(const sz of [-1,1]){
  boxMesh(.72,.16,.72,mats.stone,x+sx*(w/2-.42),deckY+ph+.02,z+sz*(d/2-.42));
  boxMesh(.32,.5,.32,mats.darkWood,x+sx*(w/2-.42),deckY+ph+.34,z+sz*(d/2-.42));
 }
 // Stair / service access room, positioned to one side so it never occupies the central running lane.
 const sx=variant%2===0?1:-1,sz=variant%3===0?1:-1;
 const hx=x-sx*w*.23,hz=z+sz*d*.2,hw=3.35,hd=3.15,hh=2.35;
 addRoofBox(hw,hh,hd,mats.plasterLight,hx,deckY+hh/2,hz,'prop');
 boxMesh(hw+.18,.16,hd+.18,mats.roofEdge,hx,deckY+hh+.08,hz);
 boxMesh(1.05,1.75,.09,mats.door,hx,deckY+.92,hz-hd/2-.055);
 boxMesh(1.45,.9,.1,mats.window,hx+1.05,deckY+1.45,hz-hd/2-.06);
 boxMesh(1.75,.12,.24,mats.wood,hx+1.05,deckY+1.0,hz-hd/2-.12);
 // A short stair run up to the access room door.
 for(let i=0;i<7;i++)boxMesh(1.25,.14,.42,mats.stone,hx,deckY+.07+i*.14,hz-hd/2-.32-i*.28);
 // Rooftop mechanical units with visible vents and a fan grille.
 const ux=x+sx*w*.25,uz=z-sz*d*.22;
 addRoofBox(2.05,.9,1.55,mats.roofMetal,ux,deckY+.45,uz,'prop');
 for(let i=0;i<5;i++)boxMesh(1.78,.055,.08,mats.metal,ux,deckY+.2+i*.15,uz-.82);
 const fan=new THREE.Mesh(new THREE.CylinderGeometry(.48,.48,.09,16),mats.darkWood);fan.position.set(ux,deckY+.94,uz);fan.castShadow=true;worldRoot.add(fan);
 const fanHub=new THREE.Mesh(new THREE.CylinderGeometry(.12,.12,.12,12),mats.metal);fanHub.position.set(ux,deckY+1.04,uz);worldRoot.add(fanHub);
 for(let i=0;i<4;i++){const blade=boxMesh(.12,.035,.72,mats.metal,ux,deckY+1.1,uz);blade.rotation.y=i*Math.PI/2;}
 // Water storage tank and its metal service pipe.
 const tx=x-sx*w*.27,tz=z-sz*d*.24;
 addRoofCylinder(tx,deckY+.92,tz,.68,1.45,mats.roofMetal,14);
 const tankCap=new THREE.Mesh(new THREE.CylinderGeometry(.68,.68,.12,14),mats.metal);tankCap.position.set(tx,deckY+1.7,tz);worldRoot.add(tankCap);
 const pipe=new THREE.Mesh(new THREE.CylinderGeometry(.07,.07,1.25,8),mats.metal);pipe.position.set(tx+.82,deckY+.62,tz+.15);worldRoot.add(pipe);
 // Planters and low greenery along one edge; leave the middle of the terrace open.
 const px=x+sx*w*.22,pz=z+sz*d*.31;
 addRoofBox(3.5,.48,.82,mats.roofEdge,px,deckY+.24,pz,'prop');
 let terV2=false;if(VEG.enabled){try{for(let i=0;i<7;i++)vegAddBush(worldRoot,px-1.35+i*.45,deckY+.46,pz,.42+(i%2)*.05,i*1.7,[.26,.46,.2],'terrace');terV2=true;}catch(err){console.warn('Terrace plants v2 failed:',err);VEG.enabled=false;}}
 if(!terV2)for(let i=0;i<7;i++){
  const plant=new THREE.Mesh(new THREE.IcosahedronGeometry(.28,1),i%2?mats.leaf2:mats.leaf);
  plant.position.set(px-1.35+i*.45,deckY+.65+(i%2)*.08,pz);plant.scale.set(1,.85,1);plant.castShadow=true;worldRoot.add(plant);
 }
 // Small roof drain channels and painted safety markings.
 for(const side of [-1,1]){
  boxMesh(2.2,.035,.12,mats.roofMark,x+side*(w*.33),deckY+.19,z-d*.33);
  boxMesh(.12,.035,2.2,mats.roofMark,x+side*(w*.33),deckY+.19,z+d*.33);
 }
 // Some buildings get a light pergola, not a closed roof, over a corner seating area.
 if(variant%3===0){
  const gx=x-w*.31,gz=z+d*.27,gw=3.2,gd=2.5,gy=deckY+2.25;
  for(const sx of [-1,1])for(const sz of [-1,1])boxMesh(.14,2.2,.14,mats.darkWood,gx+sx*gw/2,deckY+1.1,gz+sz*gd/2);
  for(let i=0;i<6;i++)boxMesh(gw,.12,.12,mats.wood,gx,gy,gz-gd/2+i*gd/5);
 }
}
function buildBuilding(spec,index,dist){const {x,z,w,d,h,style,variant}=spec;
 const openRoof=!!spec.openRoof;
 const basePlaster=style==='stone'?mats.stone:style==='white'?mats.plasterLight:style==='yellow'?mats.plasterWarm:mats.plaster;
 // Muted East-Asian town palette: every building gets a deliberate, distinct facade color.
 const facadePalette=[0xd9c5a0,0xb7cbc6,0xb97862,0x8499ad,0xd4b36f,0xb8adc4,0x899b7e,0xd6d2c8,0xa77f6b,0x9baab1,0xc6a98c,0x8f9c91];
 const plaster=basePlaster.clone();plaster.color.setHex(facadePalette[(index*5+variant*3)%facadePalette.length]);
 const trimPalette=[mats.darkWood,mats.wood,mats.windowFrameA,mats.windowFrameB,mats.windowFrameC,mats.windowFrameD];
 const trimMat=trimPalette[(index+variant*2)%trimPalette.length];
 const windowType=variant%5;
 const base=boxMesh(w,h,d,plaster,x,h/2,z);tileBoxUV(base.geometry,w,h,d,6);addSolid(base,true);addCollider(x,z,w,d,h+.29,'building');
 // Different cornices and vertical pilasters help each facade read as a separate building.
 const postMat=variant%2===0?trimMat:mats.darkWood;
 for(const sx of [-1,1])for(const sz of [-1,1])boxMesh(.42,h,.42,postMat,x+sx*(w/2-.35),h/2,z+sz*(d/2-.35));
 boxMesh(w+.48,.28,d+.48,trimMat,x,h-.18,z);
 if(variant%3===1){for(const sx of [-1,1])boxMesh(.2,h-.7,.25,mats.stone,x+sx*(w*.31),h/2,z-d/2-.16);}
 if(variant%3===2){boxMesh(w+.9,.22,.42,mats.stone,x,h*.72,z-d/2-.18);boxMesh(w+.9,.22,.42,mats.stone,x,h*.72,z+d/2+.18);}
 const floorGap=h>34?4.2:3.6;
 for(let yy=2.4;yy<h-1;yy+=floorGap){boxMesh(w+.2,.17,.22,trimMat,x,yy,z-d/2-.08);boxMesh(w+.2,.17,.22,trimMat,x,yy,z+d/2+.08);}
 // Different massing: projecting bay, side gallery or corner tower.
 if(variant%4===0){
  const bw=Math.min(w*.48,8.2),bh=Math.max(5,h*.58);
  boxMesh(bw,bh,.9,plaster,x,h*.5,z-d/2-.43);colliders.push({x,z:z-d/2-.43,halfX:bw/2,halfZ:.45,bottom:0,top:bh,kind:'building'});boxMesh(bw+.35,.2,1.12,mats.stone,x,h*.5+bh/2,z-d/2-.43);
  for(let yy=3.1;yy<bh;yy+=3.7)boxMesh(bw*.72,.1,.12,mats.wood,x,yy,z-d/2-.93);
 }
 if(variant%4===2){
  for(const side of [-1,1]){
   const bx=x+side*(w/2+.5),by=Math.min(h*.68,Math.max(7,h*.42));
   boxMesh(1.2,by*.62,d*.66,plaster,bx,by*.5,z);colliders.push({x:bx,z,halfX:.6,halfZ:d*.33,bottom:by*.19,top:by*.81,kind:'building'});
   boxMesh(2.2,.2,d*.78,mats.darkWood,bx,by*.62+.12,z);
   for(let q=-1;q<=1;q++)boxMesh(.12,.78,.12,mats.wood,bx+q*.75,by*.62+.52,z+d*.35);
  }
 }
 // Five window families: traditional shuttered, slim vertical, wide horizontal, square-grid and arched.
 for(const face of [-1,1]){
  const faceZ=z+face*(d/2+.035);
  const spacing=windowType===2?5.5:windowType===1?5.1:4.5;
  const n=Math.max(2,Math.floor(w/spacing));
  for(let j=0;j<n;j++){
   const xx=x-w*.36+j*(w*.72/Math.max(1,n-1));
   for(let yy=2.6;yy<h-1.4;yy+=floorGap){
    windowInstanceData[dist].push({x:xx,y:yy,z:faceZ,type:windowType});
    addWindowDetail(xx,yy,faceZ,face,variant,j);
   }
  }
 }
 // Front entrance framed in timber.
 boxMesh(Math.min(3,w*.22),2.5,.26,mats.darkWood,x,h/2-0.2,z-d/2-.18);boxMesh(Math.min(2.3,w*.18),2.2,.3,mats.door,x,h/2-.3,z-d/2-.34);
 if(openRoof){
  buildOpenRooftop(x,z,w,d,h,variant,[mats.roof,mats.roof2,mats.roof3][(index+variant)%3]);
 }else{
  // Main sloping gable roof; the original walkable roof and gable collision are retained.
  const roofRise=style==='pagoda'?4.2:style==='chinese'?3.3:2.5,roofW=w,roofD=d,hSpan=w*.5-.08;
  boxMesh(roofW-.08,.34,roofD-.08,mats.darkWood,x,h+.12,z);
  const roofMat=[mats.roof,mats.roof2,mats.roof3][(index+variant)%3];
  const gableShape=new THREE.Shape();gableShape.moveTo(-hSpan,-.12);gableShape.lineTo(hSpan,-.12);gableShape.lineTo(0,roofRise+.05);gableShape.closePath();
  const gableGeometry=new THREE.ExtrudeGeometry(gableShape,{depth:roofD,bevelEnabled:false,steps:1});const gableMaterial=plaster.clone();gableMaterial.map=plaster.map===texStone?texStoneG:texPlasterG;gableMaterial.side=THREE.DoubleSide;const gableFill=new THREE.Mesh(gableGeometry,gableMaterial);gableFill.position.set(x,h,z-roofD/2);gableFill.castShadow=true;gableFill.receiveShadow=true;worldRoot.add(gableFill);addSolid(gableFill,true);
  const slopeAngle=Math.atan2(roofRise,hSpan),slopeLen=Math.sqrt(hSpan**2+roofRise**2);addGableColliders(x,z,w,roofD,h,roofRise);
  const left=boxMesh(slopeLen,.28,roofD,roofMat,x-hSpan/2,h+roofRise*.48,z);tileBoxUV(left.geometry,slopeLen,.28,roofD,3);left.rotation.z=slopeAngle;addSolid(left,true);addRoofSurface(x-hSpan/2,z,hSpan/2+.14*Math.sin(slopeAngle),roofD/2,h+roofRise*.48+.14/Math.cos(slopeAngle),Math.tan(slopeAngle));
  const right=boxMesh(slopeLen,.28,roofD,roofMat,x+hSpan/2,h+roofRise*.48,z);tileBoxUV(right.geometry,slopeLen,.28,roofD,3);right.rotation.z=-slopeAngle;addSolid(right,true);addRoofSurface(x+hSpan/2,z,hSpan/2+.14*Math.sin(slopeAngle),roofD/2,h+roofRise*.48+.14/Math.cos(slopeAngle),-Math.tan(slopeAngle));
  boxMesh(.6,.55,roofD-.1,mats.darkWood,x,h+roofRise,z);addRoofSurface(x,z,.3,(roofD-.1)/2,h+roofRise+.275);
  boxMesh(roofW-.1,.25,.3,mats.darkWood,x,h+.165,z-roofD/2+.17);addRoofSurface(x,z-roofD/2+.17,(roofW-.1)/2,.15,h+.29);
  boxMesh(roofW-.1,.25,.3,mats.darkWood,x,h+.165,z+roofD/2-.17);addRoofSurface(x,z+roofD/2-.17,(roofW-.1)/2,.15,h+.29);
  if(style==='chinese'||style==='pagoda'){for(const sx of [-1,1])for(const sz of [-1,1]){const c=boxMesh(1.25,.22,1.1,roofMat,x+sx*(roofW/2-.85),h+.45,z+sz*(roofD/2-.8));c.rotation.z=-sx*.24;c.rotation.x=sz*.18;}}
  if(variant%2===0){boxMesh(w*.55,.7,.45,mats.darkWood,x,h+1.0,z+d*.22);for(let k=-1;k<=1;k++)boxMesh(.12,.65,.12,mats.wood,x+k*w*.21,h+1.1,z+d*.22);}
  if(style==='pagoda'||h>34){const tierCount=style==='pagoda'?2:1;for(let t=0;t<tierCount;t++){const ty=h*(.58+t*.23),tw=w*(.8-t*.12),td=d*(.8-t*.12);boxMesh(tw,1.1,td,mats.darkWood,x,ty,z);boxMesh(tw+2,.24,td+2,roofMat,x,ty+.72,z);}}
  // Keep the roofline clean: no chimneys on pitched / pyramid-like roofs.
  // Selected traditional roofs retain a small dormer, without a chimney stack.
  if(variant%3===1){
   boxMesh(2.2,1.1,1.0,plaster,x-w*.22,h+roofRise*.68,z);boxMesh(2.35,.24,1.15,roofMat,x-w*.22,h+roofRise*.68+.62,z);
  }
  // Extra corner turret on a few tall buildings.
  if(h>30&&variant%4===3){const tx=x+w*.34,tz=z-d*.3;const turret=new THREE.Mesh(new THREE.CylinderGeometry(1.25,1.55,3.4,8),mats.plasterWarm);turret.position.set(tx,h+roofRise+1.7,tz);turret.castShadow=true;turret.receiveShadow=true;worldRoot.add(turret);const cap=new THREE.Mesh(new THREE.ConeGeometry(1.65,1.6,8),roofMat);cap.position.set(tx,h+roofRise+4.2,tz);cap.castShadow=true;worldRoot.add(cap);}
  // Small roof-top rail / access block gives distinct navigation edges.
  if(variant%2===0){boxMesh(w*.55,.7,.45,mats.darkWood,x,h+1.0,z+d*.22);for(let k=-1;k<=1;k++)boxMesh(.12,.65,.12,mats.wood,x+k*w*.21,h+1.1,z+d*.22);}
  if(variant%3!==1){const side=variant%2===0?1:-1,bz=z+side*(d/2+1.15);boxMesh(w*.62,.18,2.2,mats.wood,x,h*.58,bz);boxMesh(w*.62,.75,.14,mats.darkWood,x,h*.58+.42,bz+side*.95);for(let q=-2;q<=2;q++)boxMesh(.12,.7,.12,mats.wood,x+q*w*.12,h*.58+.4,bz+side*.82);}
  addCollider(x,z,roofW,roofD,h+.29,'roof');
 }
 // Extra decorative sign / lantern near the entrance.
 if(index%3===0)boxMesh(1.1,1.4,.15,mats.lantern,x+w*.33,2.0,z-d/2-.55);
 buildingDetails(x,z,w,d,h,variant,index,dist,openRoof?0:(style==='pagoda'?4.2:style==='chinese'?3.3:2.5),d,[mats.roof,mats.roof2,mats.roof3][(index+variant)%3],openRoof);
}
function buildDistrict(index,cx,cz){districtCenters.push({x:cx,z:cz,index});
 paveBox(78,78,index%2?mats.cobble2:mats.cobble,cx,.02,cz,5,.08);
 // Courtyard edging and patterned pavers
 for(let i=-3;i<=3;i++){boxMesh(.14,.1,77,mats.pathLine,cx+i*11,.09,cz);boxMesh(77,.1,.14,mats.pathLine,cx,.09,cz+i*11);}
 const styleSets=[['japanese','japanese','white','stone'],['pagoda','pagoda','japanese','pagoda'],['chinese','yellow','chinese','stone'],['chinesetower','pagoda','chinese','japanese'],['mixed','japanese','chinese','mixed'],['tower','chinesetower','pagoda','tower']];const styles=styleSets[index];
 const offsets=[[-22,-22],[22,-22],[-22,22],[22,22]];
 const heightProfiles=[[15,27,38,20],[22,43,17,31],[13,34,48,23],[29,16,41,52],[19,36,14,45],[26,50,21,39]];
 // Selected buildings become open-air rooftop terraces; the remaining buildings retain traditional tiled roofs.
 const openRoofIds=new Set([1,4,7,9,12,14,17,18,21,23]);
 for(let j=0;j<4;j++){const [ox,oz]=offsets[j];let style=styles[j];let w=17+(index+j)%3*2,d=16+(index*2+j)%3*2;let h=heightProfiles[index][j];
  if(style==='pagoda'||style==='tower'||style==='chinesetower')h+=4;
  const actualStyle=style==='stone'?'stone':style==='white'?'white':style==='yellow'?'yellow':style==='japanese'?'japanese':style==='mixed'?'mixed':style==='tower'||style==='chinesetower'?'chinese':'chinese';
  const buildingId=index*4+j;
  buildBuilding({x:cx+ox,z:cz+oz,w,d,h,style:style==='pagoda'?'pagoda':style==='chinese'||style==='chinesetower'?'chinese':style==='stone'?'stone':style==='white'?'white':style==='yellow'?'yellow':'japanese',variant:j+index,openRoof:openRoofIds.has(buildingId)},buildingId,index);
 }
 // Lanterns, trees and low railings mark the alleys without blocking them.
 for(const side of [-1,1])for(let n=0;n<3;n++){const tx=cx+side*34,tz=cz-23+n*23;makeLantern(tx,tz);}
 for(const p of [[-34,-34],[34,-34],[-34,34],[34,34]])if((index+p[0])%2===0)makeTree(cx+p[0],cz+p[1],index%2===0);
 buildDistrictDetails(index,cx,cz);
}
function makeLantern(x,z){boxMesh(.22,2.1,.22,mats.darkWood,x,1.05,z);boxMesh(1.1,.15,1.1,mats.darkWood,x,2.05,z);boxMesh(1.2,.14,1.2,mats.darkWood,x,3.0,z);lanternGlowData.push({x,y:2.55,z});}
// ===================== VEGETATION v2: trees, bushes, grass, flowers =====================
// Trunks with bark texture, root flare and tapering boughs; crowns made of alpha-tested leaf cards over dark inner volumes
// (soft, outward-facing normals); layered conifers; blade-grass tufts; petal flower heads.
// Everything is generated procedurally (no assets). If anything throws, the old low-poly vegetation is used instead.
// Tweak: VEG.enabled=false (before the world is built) brings the old shapes back.
const VEG={enabled:true,mats:null,cache:{},n:0};
function vegRng(seed){let s=(seed>>>0)||1;return()=>{s=(s+0x6D2B79F5)>>>0;let t=s;t=Math.imul(t^(t>>>15),t|1);t^=t+Math.imul(t^(t>>>7),t|61);return((t^(t>>>14))>>>0)/4294967296;};}
function vegBuf(){return{p:[],n:[],u:[],c:[],i:[]};}
function vegNorm(v){const l=Math.hypot(v[0],v[1],v[2])||1;return[v[0]/l,v[1]/l,v[2]/l];}
function vegCross(a,b){return[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];}
// quad centred on c: width along r, height along u. Visible from the side of r x u (and from the back too when `double`).
function vegQuad(B,c,r,u,w,h,nrm,col,col2,double,uv){
 uv=uv||[0,0,1,1];const hw=w/2,hh=h/2,cs=[[-1,-1],[1,-1],[1,1],[-1,1]];
 for(let pass=0;pass<(double?2:1);pass++){
  const base=B.p.length/3;
  for(let k=0;k<4;k++){const sx=cs[k][0],sy=cs[k][1],cc=sy<0?col:col2;
   B.p.push(c[0]+r[0]*hw*sx+u[0]*hh*sy,c[1]+r[1]*hw*sx+u[1]*hh*sy,c[2]+r[2]*hw*sx+u[2]*hh*sy);
   B.n.push(nrm[0],nrm[1],nrm[2]);B.u.push(sx<0?uv[0]:uv[2],sy<0?uv[1]:uv[3]);B.c.push(cc[0],cc[1],cc[2]);}
  if(pass===0)B.i.push(base,base+1,base+2,base,base+2,base+3);else B.i.push(base,base+2,base+1,base,base+3,base+2);
 }
}
// tapered tube along the points pts (radius radii[k] at each ring), outward normals
function vegTube(B,pts,radii,seg,vScale,uRep,knob,rng,col){
 const K=pts.length,dv=[pts[K-1][0]-pts[0][0],pts[K-1][1]-pts[0][1],pts[K-1][2]-pts[0][2]],ref=Math.abs(vegNorm(dv)[1])<.9?[0,1,0]:[1,0,0];
 const base=B.p.length/3,nz=[];for(let q=0;q<K*seg;q++)nz.push(rng()-.5);
 let acc=0;
 for(let k=0;k<K;k++){
  const a=pts[Math.max(0,k-1)],b=pts[Math.min(K-1,k+1)],T=vegNorm([b[0]-a[0],b[1]-a[1],b[2]-a[2]]);
  if(k>0)acc+=Math.hypot(pts[k][0]-pts[k-1][0],pts[k][1]-pts[k-1][1],pts[k][2]-pts[k-1][2]);
  let Bv=vegCross(T,ref);Bv=vegNorm(Bv);const Nv=vegCross(Bv,T);
  for(let j=0;j<=seg;j++){
   const jj=j%seg,an=jj/seg*6.2832,ca=Math.cos(an),sa=Math.sin(an),d=[Nv[0]*ca+Bv[0]*sa,Nv[1]*ca+Bv[1]*sa,Nv[2]*ca+Bv[2]*sa],rr=radii[k]*(1+knob*nz[k*seg+jj]);
   B.p.push(pts[k][0]+d[0]*rr,pts[k][1]+d[1]*rr,pts[k][2]+d[2]*rr);B.n.push(d[0],d[1],d[2]);B.u.push(j/seg*uRep,acc/vScale);
   const sh=.85+.3*(nz[k*seg+jj]+.5);B.c.push(col[0]*sh,col[1]*sh,col[2]*sh);
  }
 }
 for(let k=0;k<K-1;k++)for(let j=0;j<seg;j++){const i0=base+k*(seg+1)+j,i1=i0+1,i2=i0+seg+1,i3=i2+1;B.i.push(i0,i1,i2,i1,i3,i2);}
}
function vegSphere(B,c,rad,scl,segU,segV,col){
 const base=B.p.length/3;
 for(let i=0;i<=segV;i++)for(let j=0;j<=segU;j++){
  const th=i/segV*Math.PI,ph=j/segU*6.2832,d=[Math.sin(th)*Math.cos(ph),Math.cos(th),Math.sin(th)*Math.sin(ph)];
  B.p.push(c[0]+d[0]*rad*scl[0],c[1]+d[1]*rad*scl[1],c[2]+d[2]*rad*scl[2]);B.n.push(d[0],d[1],d[2]);B.u.push(j/segU,i/segV);B.c.push(col[0],col[1],col[2]);}
 for(let i=0;i<segV;i++)for(let j=0;j<segU;j++){const a=base+i*(segU+1)+j,b=a+segU+1;B.i.push(a,a+1,b,a+1,b+1,b);}
}
function vegCone(B,c,r,h,seg,col){   // apex up, base ring at c
 const base=B.p.length/3;
 for(let j=0;j<=seg;j++){const ph=j/seg*6.2832,ca=Math.cos(ph),sa=Math.sin(ph),nn=vegNorm([ca*h,r,sa*h]);
  B.p.push(c[0]+ca*r,c[1],c[2]+sa*r);B.n.push(nn[0],nn[1],nn[2]);B.u.push(.5,.5);B.c.push(col[0],col[1],col[2]);
  B.p.push(c[0],c[1]+h,c[2]);B.n.push(nn[0],nn[1],nn[2]);B.u.push(.5,.5);B.c.push(col[0],col[1],col[2]);}
 for(let j=0;j<seg;j++){const a=base+j*2;B.i.push(a,a+1,a+2);}
}
// ---------------- textures (mono: the colour comes from vertex / instance colours) ----------------
function vegCanvas(w,h){const c=document.createElement('canvas');c.width=w;c.height=h;return c;}
function vegTexLeaf(blossom){
 const S=512,c=vegCanvas(S,S),x=c.getContext('2d'),rng=vegRng(blossom?91:17),items=[];
 for(let i=0;i<(blossom?340:300);i++){const a=rng()*6.2832,rad=Math.sqrt(rng())*S*.45*(.86+.14*Math.sin(a*3+1));
  items.push({px:S/2+Math.cos(a)*rad,py:S/2+Math.sin(a)*rad*.9,rad,rot:a+(rng()-.5)*1.6,len:(blossom?20:42)+rng()*(blossom?12:30)});}
 items.sort((p,q)=>p.rad-q.rad);   // dark inner leaves first, lighter outer leaves on top: the card reads as a small volume
 for(const it of items){
  const t=it.rad/(S*.45),v=Math.round(255*Math.min(1,.5+.5*t+(rng()-.5)*.16)),L=it.len,W=L*.46;
  x.save();x.translate(it.px,it.py);x.rotate(it.rot);x.fillStyle='rgb('+v+','+v+','+v+')';
  if(blossom){for(let k=0;k<5;k++){x.rotate(1.2566);x.beginPath();x.ellipse(L*.42,0,L*.5,L*.33,0,0,6.2832);x.fill();}
   x.fillStyle='rgb('+Math.round(v*.5)+','+Math.round(v*.5)+','+Math.round(v*.5)+')';x.beginPath();x.arc(0,0,L*.14,0,6.2832);x.fill();}
  else{x.beginPath();x.moveTo(0,0);x.bezierCurveTo(L*.25,-W*.6,L*.7,-W*.55,L,0);x.bezierCurveTo(L*.7,W*.55,L*.25,W*.6,0,0);x.fill();
   x.strokeStyle='rgba(0,0,0,.28)';x.lineWidth=1.3;x.beginPath();x.moveTo(0,0);x.lineTo(L*.92,0);x.stroke();}
  x.restore();}
 return c;
}
function vegTexFir(){
 const c=vegCanvas(256,256),x=c.getContext('2d'),rng=vegRng(33);x.lineCap='round';
 x.strokeStyle='rgb(120,120,120)';x.lineWidth=3.2;x.beginPath();x.moveTo(128,254);x.lineTo(128,6);x.stroke();
 for(let s=0;s<24;s++){const t=s/23,y=250-t*232,hl=Math.pow(1-t,.75)*112+7;
  for(const side of [-1,1]){const ex=128+side*hl,ey=y-hl*.5;
   x.strokeStyle='rgb(135,135,135)';x.lineWidth=2.2;x.beginPath();x.moveTo(128,y);x.lineTo(ex,ey);x.stroke();
   for(let q=1;q<=15;q++){const u=q/15,bx=128+side*hl*u,by=y-hl*.5*u,ln=10+rng()*9;
    for(const ang of [-.95,.95]){const dx=side*Math.cos(.46+ang)*ln,dy=-Math.sin(.46+ang)*ln,v=Math.round(255*(.62+.38*rng()));
     x.strokeStyle='rgb('+v+','+v+','+v+')';x.lineWidth=1.7;x.beginPath();x.moveTo(bx,by);x.lineTo(bx+dx,by+dy);x.stroke();}}}}
 return c;
}
function vegTexBlade(){
 const c=vegCanvas(256,256),x=c.getContext('2d'),rng=vegRng(5);
 for(let i=0;i<20;i++){const bx=60+rng()*136,h=100+rng()*150,w=7+rng()*8,bend=(rng()-.5)*96,g=x.createLinearGradient(0,256,0,256-h),vt=Math.round(215+40*rng());
  g.addColorStop(0,'rgb(150,150,150)');g.addColorStop(1,'rgb('+vt+','+vt+','+vt+')');x.fillStyle=g;
  x.beginPath();x.moveTo(bx-w/2,256);x.quadraticCurveTo(bx-w/2+bend*.15,256-h*.6,bx+bend,256-h);x.quadraticCurveTo(bx+w/2+bend*.15,256-h*.6,bx+w/2,256);x.closePath();x.fill();}
 return c;
}
function vegTexFlower(){
 const c=vegCanvas(128,128),x=c.getContext('2d');
 for(let k=0;k<6;k++){x.save();x.translate(64,64);x.rotate(k*1.0472);const g=x.createRadialGradient(18,0,2,34,0,28);g.addColorStop(0,'rgb(205,205,205)');g.addColorStop(1,'rgb(255,255,255)');
  x.fillStyle=g;x.beginPath();x.ellipse(32,0,28,15,0,0,6.2832);x.fill();x.restore();}
 x.fillStyle='rgb(110,110,110)';x.beginPath();x.arc(64,64,14,0,6.2832);x.fill();
 return c;
}
function vegTexBark(){
 const c=vegCanvas(128,256),x=c.getContext('2d'),rng=vegRng(71);
 x.fillStyle='rgb(168,168,168)';x.fillRect(0,0,128,256);
 for(let i=0;i<90;i++){const px=rng()*128,w=1+rng()*4.5,len=50+rng()*190,y0=rng()*256,dark=rng()<.72;
  x.strokeStyle=dark?'rgba(0,0,0,'+(.14+.34*rng())+')':'rgba(255,255,255,'+(.08+.12*rng())+')';x.lineWidth=w;
  for(const oy of [0,-256]){x.beginPath();let yy=y0+oy,xx=px;x.moveTo(xx,yy);for(let s=0;s<8;s++){yy+=len/8;xx+=(rng()-.5)*3;x.lineTo(xx,yy);}x.stroke();}}
 x.strokeStyle='rgba(0,0,0,.22)';x.lineWidth=1.4;
 for(let i=0;i<46;i++){const px=rng()*128,py=rng()*256,w=6+rng()*18;x.beginPath();x.moveTo(px,py);x.lineTo(px+w,py+(rng()-.5)*3);x.stroke();}
 return c;
}
// ---------------- geometry builders (plain data; turned into BufferGeometry by vegGeo) ----------------
function vegBuildTree(kind,variant){
 const seed=(kind==='fir'?7000:kind==='sakura'?9000:5000)+variant*131;
 if(kind==='fir')return vegBuildFir(seed,{height:8.6+variant*.5,levels:12,wide:1+variant*.06,palette:[[.075,.2,.115],[.095,.23,.12],[.06,.17,.1]],coreCol:[.025,.07,.05]});
 if(kind==='sakura')return vegBuildOak(seed,{trunkH:3.5,trunkR:.58,lean:.8,boughs:7,elev:[.45,.95],boughLen:[1.7,2.5],curl:.3,clumpR:1.65,topLift:1.0,cards:26,cardSize:1.9,
  palette:[[.62,.2,.3],[.7,.3,.4],[.55,.16,.27],[.74,.42,.52]],coreCol:[.16,.05,.08],blossom:true});
 return vegBuildOak(seed,{trunkH:3.3+variant*.3,trunkR:.5,lean:.5,boughs:5+(variant%2),elev:[.7,1.1],boughLen:[1.2,1.95],curl:.25,clumpR:1.5,topLift:1.1,cards:24,cardSize:1.95,
  palette:[[.15,.32,.12],[.2,.36,.11],[.11,.27,.11],[.24,.34,.12]],coreCol:[.035,.085,.04]});
}
function vegBuildOak(seed,o){
 const rng=vegRng(seed),bark=vegBuf(),leaf=vegBuf(),core=vegBuf(),Ht=o.trunkH,K=9,tp=[],tr=[];
 const ax=rng()*6.2832,lean=o.lean*(.6+rng()*.8),ph=rng()*6.2832;
 for(let k=0;k<K;k++){const t=k/(K-1),dx=lean*(t*t+.18*Math.sin(t*6+ph)*t);
  tp.push([Math.cos(ax)*dx,-.15+t*(Ht+.15),Math.sin(ax)*dx]);tr.push(o.trunkR*(1-.6*t)*(1+.7*Math.exp(-t*10)));}
 vegTube(bark,tp,tr,10,1.7,2,.12,rng,[1,1,1]);
 const lerpK=(arr,t)=>{const f=t*(K-1),i=Math.min(K-2,Math.floor(f)),u=f-i;return Array.isArray(arr[0])?[0,1,2].map(a=>arr[i][a]*(1-u)+arr[i+1][a]*u):arr[i]*(1-u)+arr[i+1]*u;};
 const clumps=[],nB=o.boughs;
 for(let i=0;i<nB;i++){
  const tt=.5+rng()*.42,P=lerpK(tp,tt),az=i/nB*6.2832+rng()*.8,el=o.elev[0]+rng()*(o.elev[1]-o.elev[0]),len=o.boughLen[0]+rng()*(o.boughLen[1]-o.boughLen[0]);
  const d=[Math.cos(az)*Math.cos(el),Math.sin(el),Math.sin(az)*Math.cos(el)],pts=[],rb=lerpK(tr,tt)*.55;
  for(let k=0;k<4;k++){const f=k/3;pts.push([P[0]+d[0]*len*f,P[1]+d[1]*len*f+o.curl*len*f*f,P[2]+d[2]*len*f]);}
  vegTube(bark,pts,[rb,rb*.72,rb*.46,rb*.22],6,1.2,1,.1,rng,[1,1,1]);
  clumps.push({c:[pts[3][0]+d[0]*.3,pts[3][1]+.25,pts[3][2]+d[2]*.3],R:o.clumpR*(.9+rng()*.25)});
  clumps.push({c:[pts[2][0]+(rng()-.5)*.8,pts[2][1]+.5+rng()*.3,pts[2][2]+(rng()-.5)*.8],R:o.clumpR*(.7+rng()*.2)});
 }
 const top=tp[K-1];
 clumps.push({c:[top[0],top[1]+o.topLift,top[2]],R:o.clumpR*1.1});
 clumps.push({c:[top[0]+(rng()-.5),top[1]+o.topLift*.45,top[2]+(rng()-.5)],R:o.clumpR*.95});
 let cc=[0,0,0],minY=1e9,maxY=-1e9;
 for(const k of clumps){cc[0]+=k.c[0];cc[1]+=k.c[1];cc[2]+=k.c[2];minY=Math.min(minY,k.c[1]-k.R);maxY=Math.max(maxY,k.c[1]+k.R);}
 cc=cc.map(v=>v/clumps.length);
 for(const k of clumps){
  const n=Math.max(6,Math.round(o.cards*k.R/o.clumpR));
  for(let q=0;q<n;q++){
   const v=vegNorm([rng()-.5,rng()-.5,rng()-.5]),rr=k.R*(.4+.6*Math.cbrt(rng())),pos=[k.c[0]+v[0]*rr,k.c[1]+v[1]*rr*.85,k.c[2]+v[2]*rr];
   const n1=vegNorm([pos[0]-k.c[0],pos[1]-k.c[1],pos[2]-k.c[2]]),n2=vegNorm([pos[0]-cc[0],pos[1]-cc[1],pos[2]-cc[2]]);
   const nm=vegNorm([n1[0]*.5+n2[0]*.5,n1[1]*.5+n2[1]*.5+.22,n1[2]*.5+n2[2]*.5]);
   const f=vegNorm([nm[0]+(rng()-.5)*.5,nm[1]+(rng()-.5)*.5,nm[2]+(rng()-.5)*.5]);
   let rt=vegCross([0,1,0],f);if(Math.hypot(rt[0],rt[1],rt[2])<.05)rt=[1,0,0];rt=vegNorm(rt);
   const up=vegCross(f,rt),ang=rng()*6.2832,ca=Math.cos(ang),sa=Math.sin(ang);
   const r2=[rt[0]*ca+up[0]*sa,rt[1]*ca+up[1]*sa,rt[2]*ca+up[2]*sa],u2=[-rt[0]*sa+up[0]*ca,-rt[1]*sa+up[1]*ca,-rt[2]*sa+up[2]*ca];
   const hgt=Math.min(1,Math.max(0,(pos[1]-minY)/(maxY-minY))),br=.6+.5*hgt+(rng()-.5)*.2,pc=o.palette[Math.floor(rng()*o.palette.length)];
   const col=[pc[0]*br,pc[1]*br,pc[2]*br],col2=[col[0]*1.15,col[1]*1.15,col[2]*1.15],sz=o.cardSize*(.8+rng()*.45);
   vegQuad(leaf,pos,r2,u2,sz,sz,nm,col,col2,true);
  }
  vegSphere(core,k.c,k.R*.5,[1,.8,1],7,5,o.coreCol);
 }
 return{bark,leaf,core};
}
function vegBuildFir(seed,o){
 const rng=vegRng(seed),bark=vegBuf(),leaf=vegBuf(),core=vegBuf(),H=o.height,tp=[],tr=[],K=8,ax=rng()*6.2832,lean=.25*rng();
 for(let k=0;k<K;k++){const t=k/(K-1);tp.push([Math.cos(ax)*lean*t*t,-.15+t*(H*.97+.15),Math.sin(ax)*lean*t*t]);tr.push(.4*(1-.93*t)*(1+.6*Math.exp(-t*12)));}
 vegTube(bark,tp,tr,9,1.7,2,.1,rng,[1,1,1]);
 const L=o.levels;
 for(let l=0;l<L;l++){
  const f=l/(L-1),y=1.5+f*(H-1.5-.5),R=(2.7*Math.pow(1-f,.9)+.4)*o.wide,nF=6+Math.round(R*1.7),ox=Math.cos(ax)*lean*(y/H)*(y/H),oz=Math.sin(ax)*lean*(y/H)*(y/H);
  for(let k=0;k<nF;k++){
   const az=k/nF*6.2832+l*.7+(rng()-.5)*.5,drop=.26+rng()*.22,ch=Math.cos(az),sh=Math.sin(az),dir=[ch*Math.cos(drop),-Math.sin(drop),sh*Math.cos(drop)],t=[-sh,0,ch];
   const len=R*(.9+rng()*.25),b0=[ox+ch*.12,y,oz+sh*.12],ctr=[b0[0]+dir[0]*len/2,b0[1]+dir[1]*len/2,b0[2]+dir[2]*len/2],w=len*(.85+.3*rng());
   const nm=vegNorm([ch*.45,.85,sh*.45]),br=.7+.45*f+(rng()-.5)*.16,pc=o.palette[Math.floor(rng()*o.palette.length)];
   const col=[pc[0]*br,pc[1]*br,pc[2]*br],col2=[col[0]*1.18,col[1]*1.18,col[2]*1.18];
   vegQuad(leaf,ctr,t,dir,w,len,nm,col,col2,true);
   if(rng()<.5)vegQuad(leaf,[ctr[0],ctr[1]+len*.12,ctr[2]],[0,1,0],dir,len*.55,len*.92,nm,col,col2,true);
  }
  vegCone(core,[ox,y-.35,oz],R*.5,1.5+R*.2,9,o.coreCol);
 }
 const tip=tp[K-1];
 for(let q=0;q<2;q++){const a=q*1.5708,r=[Math.cos(a),0,Math.sin(a)];vegQuad(leaf,[tip[0],tip[1]-.3,tip[2]],r,[0,1,0],.9,1.7,[0,1,0],[.05,.14,.08],[.07,.19,.1],true);}
 return{bark,leaf,core};
}
function vegBuildBush(tint){
 const rng=vegRng(4242),leaf=vegBuf(),core=vegBuf(),T=tint||[1,1,1],cen=[0,.34,0];
 const cl=[[0,.46,0,.58],[.42,.36,.1,.46],[-.4,.34,-.08,.48],[.06,.32,-.42,.44],[.1,.3,.42,.44]];
 for(const k of cl){
  for(let q=0;q<8;q++){
   const v=vegNorm([rng()-.5,rng()*.9-.15,rng()-.5]),rr=k[3]*(.55+.45*rng());
   const pos=[k[0]+v[0]*rr,Math.max(.1,k[1]+v[1]*rr),k[2]+v[2]*rr],n1=vegNorm([pos[0]-cen[0],pos[1]-cen[1],pos[2]-cen[2]]),nm=vegNorm([n1[0],n1[1]+.35,n1[2]]);
   const f=vegNorm([nm[0]+(rng()-.5)*.7,nm[1]+(rng()-.5)*.7,nm[2]+(rng()-.5)*.7]);let rt=vegCross([0,1,0],f);if(Math.hypot(rt[0],rt[1],rt[2])<.05)rt=[1,0,0];rt=vegNorm(rt);
   const up=vegCross(f,rt),ang=rng()*6.2832,ca=Math.cos(ang),sa=Math.sin(ang);
   const r2=[rt[0]*ca+up[0]*sa,rt[1]*ca+up[1]*sa,rt[2]*ca+up[2]*sa],u2=[-rt[0]*sa+up[0]*ca,-rt[1]*sa+up[1]*ca,-rt[2]*sa+up[2]*ca];
   const br=.62+.5*Math.min(1,pos[1]/.9)+(rng()-.5)*.16,sz=.85*(.8+rng()*.45);
   vegQuad(leaf,pos,r2,u2,sz,sz,nm,[T[0]*br,T[1]*br,T[2]*br],[T[0]*br*1.15,T[1]*br*1.15,T[2]*br*1.15],true);
  }
  vegSphere(core,[k[0],k[1],k[2]],k[3]*.62,[1,.8,1],6,4,[.4*T[0],.4*T[1],.4*T[2]]);
 }
 return{leaf,core};
}
function vegBuildTuft(){
 const B=vegBuf(),h=.62,w=.8;
 for(let k=0;k<3;k++){const a=k*1.0472+.3;vegQuad(B,[0,h/2,0],[Math.cos(a),0,Math.sin(a)],[0,1,0],w,h,[0,1,0],[.55,.55,.55],[1.05,1.05,1.05],true);}
 return B;
}
function vegBuildFlower(tint){
 const B=vegBuf(),T=tint||[1,1,1],s=.36;
 vegQuad(B,[0,0,0],[1,0,0],[0,0,1],s,s,[0,1,0],T,T,true);
 for(let k=0;k<2;k++){const a=k*1.5708+.4;vegQuad(B,[0,0,0],[Math.cos(a),0,Math.sin(a)],[0,1,0],s*.9,s*.9,[0,1,0],T,T,true);}
 return B;
}
// ---------------- three.js binding ----------------
function vegGeo(B){
 const g=new THREE.BufferGeometry();
 g.setAttribute('position',new THREE.Float32BufferAttribute(B.p,3));g.setAttribute('normal',new THREE.Float32BufferAttribute(B.n,3));
 g.setAttribute('uv',new THREE.Float32BufferAttribute(B.u,2));g.setAttribute('color',new THREE.Float32BufferAttribute(B.c,3));
 g.setIndex(B.i);g.computeBoundingBox();g.computeBoundingSphere();return g;
}
function vegMats(){
 if(VEG.mats)return VEG.mats;
 const tex=(c,rep)=>{const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;t.anisotropy=4;if(rep)t.wrapS=t.wrapT=THREE.RepeatWrapping;return t;};
 const cut=(map,a)=>new THREE.MeshStandardMaterial({map,alphaTest:a||.5,vertexColors:true,roughness:.92,metalness:0});
 VEG.mats={leaf:cut(tex(vegTexLeaf(false))),blossom:cut(tex(vegTexLeaf(true))),fir:cut(tex(vegTexFir())),grass:cut(tex(vegTexBlade()),.42),flower:cut(tex(vegTexFlower()),.5),
  bark:new THREE.MeshStandardMaterial({map:tex(vegTexBark(),true),color:0x6e5846,vertexColors:true,roughness:1}),
  core:new THREE.MeshStandardMaterial({vertexColors:true,roughness:1})};
 return VEG.mats;
}
function vegCached(key,fn){return VEG.cache[key]||(VEG.cache[key]=fn());}
function vegAddTree(parent,kind,variant,x,z,rotY,scale){
 const P=vegCached('tree:'+kind+variant,()=>{const B=vegBuildTree(kind,variant);return{bark:vegGeo(B.bark),leaf:vegGeo(B.leaf),core:vegGeo(B.core)};}),M=vegMats();
 const g=new THREE.Group();g.position.set(x,0,z);g.rotation.y=rotY;g.scale.setScalar(scale);
 const bark=new THREE.Mesh(P.bark,M.bark),leaf=new THREE.Mesh(P.leaf,kind==='fir'?M.fir:kind==='sakura'?M.blossom:M.leaf),core=new THREE.Mesh(P.core,M.core);
 bark.name='TreeTrunk';leaf.name='TreeLeaves';core.name='TreeCore';
 for(const m of [bark,leaf,core]){m.castShadow=false;m.receiveShadow=false;g.add(m);}
 parent.add(g);return g;
}
function vegAddBush(parent,x,y,z,s,rotY,tint,key){
 const P=vegCached('bush:'+key,()=>{const B=vegBuildBush(tint);return{leaf:vegGeo(B.leaf),core:vegGeo(B.core)};}),M=vegMats();
 const g=new THREE.Group();g.position.set(x,y,z);g.rotation.y=rotY;g.scale.setScalar(s);
 const l=new THREE.Mesh(P.leaf,M.leaf),c=new THREE.Mesh(P.core,M.core);l.name='PotPlant';c.name='PotPlant';
 g.add(l);g.add(c);parent.add(g);return g;
}
function vegAddFlowers(parent,x,y,z,fi){
 const tints=[[.68,.08,.17],[.88,.62,.07],[.8,.78,.85]],M=vegMats(),P=vegCached('flower:'+fi,()=>vegGeo(vegBuildFlower(tints[fi%3])));
 for(const [dx,dy,dz] of [[0,.12,0],[.16,.0,.08],[-.12,.03,-.12]]){const m=new THREE.Mesh(P,M.flower);m.name='PotPlant';m.position.set(x+dx,y+dy,z+dz);parent.add(m);}
}
let _vegTreeN=0;
function vegTreeHash(x,z){let h=Math.imul(Math.round(x*7.3)^Math.imul(Math.round(z*3.1),374761393),2654435761)>>>0;h^=h>>>13;return(Math.imul(h,1274126177)>>>0)/4294967296;}
function makeTree(x,z,evergreen=false){
 if(VEG.enabled){
  try{const h=vegTreeHash(x,z);vegAddTree(worldRoot,evergreen?'fir':'oak',(_vegTreeN++)%(evergreen?3:4),x,z,h*6.2832,.86+h*.26);return;}
  catch(err){console.warn('Tree v2 failed; using the old trees:',err);VEG.enabled=false;}
 }
 makeTreeLegacy(x,z,evergreen);
}
function makeTreeLegacy(x,z,evergreen=false){const g=new THREE.Group();g.position.set(x,0,z);worldRoot.add(g);const height=evergreen?8:6.2;const trunk=new THREE.Mesh(new THREE.CylinderGeometry(.35,.55,height*.55,7),mats.treeTrunk);trunk.position.y=height*.27;trunk.castShadow=false;trunk.receiveShadow=false;g.add(trunk);if(evergreen){for(let i=0;i<3;i++){const cone=new THREE.Mesh(new THREE.ConeGeometry(2.6-i*.45,3.3,7),i%2?mats.leaf2:mats.leaf);cone.position.y=height*.55+i*1.25;cone.castShadow=false;cone.receiveShadow=false;g.add(cone);}}else{const crown=new THREE.Mesh(new THREE.IcosahedronGeometry(2.3,1),mats.leaf);crown.position.y=height*.67;crown.scale.set(1,1.2,1);crown.castShadow=false;crown.receiveShadow=false;g.add(crown);for(let i=0;i<4;i++){const cloud=new THREE.Mesh(new THREE.IcosahedronGeometry(1.2,1),i%2?mats.leaf2:mats.leaf);cloud.position.set(Math.sin(i*1.6)*1.5,height*.62+(i%2)*1.2,Math.cos(i*1.6)*1.4);cloud.castShadow=false;cloud.receiveShadow=false;g.add(cloud);}}
}
function buildOuterWall(){const r=WORLD.wallRadius,segments=96,segW=2*Math.PI*r/segments;
 for(let i=0;i<segments;i++){const a=i/segments*Math.PI*2,x=Math.cos(a)*r,z=Math.sin(a)*r;const block=orientedBox(segW+1,WORLD.wallHeight,7,mats.wallStone,v3(x,WORLD.wallHeight/2,z),-a+Math.PI/2);tileBoxUV(block.geometry,segW+1,WORLD.wallHeight,7,5);block.castShadow=(i%8===0);block.receiveShadow=true;addSolid(block,true);if(i%4===0){const tower=new THREE.Mesh(new THREE.CylinderGeometry(3.3,3.8,4.5,8),mats.stone);tower.position.set(x,WORLD.wallHeight+2,z);tower.castShadow=true;tower.receiveShadow=true;worldRoot.add(tower);boxMesh(7,.7,7,mats.darkWood,x,WORLD.wallHeight+4.2,z);}
  // crenellations along top, repeated around the circumference
  for(const side of [-1,1]){const bx=x+Math.cos(a)*3.1*side,bz=z+Math.sin(a)*3.1*side;boxMesh(segW*.42,1.6,1.1,mats.stone,bx,WORLD.wallHeight+.8,bz,worldRoot,-a+Math.PI/2);}
 }
 // Decorative inner gate / arch, still leaves the playable world safely enclosed.
 const gx=0,gz=-r;boxMesh(29,18,10,mats.stone,gx,9,gz);boxMesh(15,13,10,mats.path,gx,6.5,gz+0.2);boxMesh(31,1.2,12,mats.darkWood,gx,18.4,gz);boxMesh(3,21,12,mats.stone,-14,10.5,gz);boxMesh(3,21,12,mats.stone,14,10.5,gz);
}
function createRepeatedInstances(){
 // One instanced batch per district + window family keeps detailed facades inexpensive to render.
 const windowGeometries=[
  new THREE.BoxGeometry(1.15,1.45,.14),
  new THREE.BoxGeometry(.82,1.82,.14),
  new THREE.BoxGeometry(1.82,.98,.14),
  new THREE.BoxGeometry(1.22,1.12,.14),
  (()=>{const sh=new THREE.Shape();sh.moveTo(-.68,-.88);sh.lineTo(.68,-.88);sh.lineTo(.68,.36);sh.quadraticCurveTo(.68,.9,0,.9);sh.quadraticCurveTo(-.68,.9,-.68,.36);sh.closePath();const g=new THREE.ExtrudeGeometry(sh,{depth:.14,bevelEnabled:false,steps:1});g.translate(0,0,-.07);return g;})()
 ];
 const glassMaterials=[mats.window,mats.windowBlue,mats.windowWarm,mats.windowGreen,mats.windowBlue];
 for(const material of glassMaterials)material.side=THREE.DoubleSide;
 const dummy=new THREE.Object3D();
 for(let district=0;district<windowInstanceData.length;district++){
  const items=windowInstanceData[district];if(!items.length)continue;
  for(let type=0;type<5;type++){
   const subset=items.filter(p=>(p.type||0)===type);if(!subset.length)continue;
   const mesh=new THREE.InstancedMesh(windowGeometries[type],glassMaterials[type],subset.length);
   mesh.name='WindowInstances_D'+district+'_T'+type;mesh.castShadow=false;mesh.receiveShadow=false;mesh.instanceMatrix.setUsage(THREE.StaticDrawUsage);
   for(let i=0;i<subset.length;i++){const p=subset[i];dummy.position.set(p.x,p.y,p.z);dummy.rotation.set(0,0,0);dummy.scale.set(1,1,1);dummy.updateMatrix();mesh.setMatrixAt(i,dummy.matrix);}
   mesh.computeBoundingBox();mesh.computeBoundingSphere();worldRoot.add(mesh);
  }
 }
 // Lantern emissive blocks use instancing instead of individual meshes and dynamic lights.
 if(lanternGlowData.length){
  const glowGeo=new THREE.BoxGeometry(.76,.76,.76);const glowMesh=new THREE.InstancedMesh(glowGeo,mats.lanternGlow,lanternGlowData.length);glowMesh.name='LanternGlowInstances';glowMesh.castShadow=false;glowMesh.receiveShadow=false;glowMesh.instanceMatrix.setUsage(THREE.StaticDrawUsage);
  const glowDummy=new THREE.Object3D();for(let i=0;i<lanternGlowData.length;i++){const p=lanternGlowData[i];glowDummy.position.set(p.x,p.y,p.z);glowDummy.updateMatrix();glowMesh.setMatrixAt(i,glowDummy.matrix);}glowMesh.computeBoundingBox();glowMesh.computeBoundingSphere();worldRoot.add(glowMesh);
  // A soft translucent ground decal fakes a pool of warm lantern light without PointLights.
  const c=document.createElement('canvas');c.width=c.height=64;const ctx=c.getContext('2d');const grad=ctx.createRadialGradient(32,32,2,32,32,32);grad.addColorStop(0,'rgba(255,176,96,.7)');grad.addColorStop(.5,'rgba(255,150,66,.3)');grad.addColorStop(1,'rgba(255,145,56,0)');ctx.fillStyle=grad;ctx.fillRect(0,0,64,64);
  const glowTexture=new THREE.CanvasTexture(c);glowTexture.colorSpace=THREE.SRGBColorSpace;
  const patchMaterial=new THREE.MeshBasicMaterial({map:glowTexture,transparent:true,opacity:.95,depthWrite:false,side:THREE.DoubleSide,toneMapped:false});
  const patchGeo=new THREE.PlaneGeometry(7.5,7.5);const patches=new THREE.InstancedMesh(patchGeo,patchMaterial,lanternGlowData.length);patches.name='LanternFakeLightPatches';patches.castShadow=false;patches.receiveShadow=false;patches.instanceMatrix.setUsage(THREE.StaticDrawUsage);
  const patchDummy=new THREE.Object3D();for(let i=0;i<lanternGlowData.length;i++){const p=lanternGlowData[i];patchDummy.position.set(p.x,.071,p.z);patchDummy.rotation.set(-Math.PI/2,0,0);patchDummy.scale.set(1,1,1);patchDummy.updateMatrix();patches.setMatrixAt(i,patchDummy.matrix);}patches.computeBoundingBox();patches.computeBoundingSphere();worldRoot.add(patches);
 }
}
function batchStaticBoxMeshes(){
 // Merge non-interactive architectural trim into spatial/material batches. Main building
 // masses, walkable roofs and grappling targets remain individual collision/raycast meshes.
 worldRoot.updateMatrixWorld(true);
 const protectedMeshes=new Set([...solidMeshes,...targetMeshes]);const groups=new Map();const worldPos=new THREE.Vector3();
 for(const mesh of staticBoxCandidates){if(protectedMeshes.has(mesh)||!mesh.parent)continue;mesh.updateWorldMatrix(true,false);mesh.getWorldPosition(worldPos);
  const chunkX=Math.round(worldPos.x/88),chunkZ=Math.round(worldPos.z/120);const key=mesh.material.uuid+'|'+chunkX+'|'+chunkZ;
  if(!groups.has(key))groups.set(key,{material:mesh.material,meshes:[]});groups.get(key).meshes.push(mesh);
 }
 for(const group of groups.values()){
  const meshes=group.meshes;if(meshes.length<2){for(const mesh of meshes){mesh.castShadow=false;mesh.receiveShadow=false;}continue;}const geometries=[];
  for(const mesh of meshes){const source=mesh.geometry.clone();source.applyMatrix4(mesh.matrixWorld);let geometry=source;if(source.index){geometry=source.toNonIndexed();source.dispose();}geometries.push(geometry);}
  const names=Object.keys(geometries[0].attributes);const mergedGeometry=new THREE.BufferGeometry();
  for(const name of names){const first=geometries[0].getAttribute(name);let total=0;for(const geometry of geometries)total+=geometry.getAttribute(name).array.length;const data=new Float32Array(total);let offset=0;for(const geometry of geometries){const attr=geometry.getAttribute(name);data.set(attr.array,offset);offset+=attr.array.length;}mergedGeometry.setAttribute(name,new THREE.BufferAttribute(data,first.itemSize));}
  mergedGeometry.computeBoundingBox();mergedGeometry.computeBoundingSphere();const mergedMesh=new THREE.Mesh(mergedGeometry,group.material);mergedMesh.name='MergedStatic_'+group.material.name;mergedMesh.castShadow=false;mergedMesh.receiveShadow=false;worldRoot.add(mergedMesh);
  for(let i=0;i<meshes.length;i++){const mesh=meshes[i],parent=mesh.parent;parent.remove(mesh);mesh.geometry.dispose();if(parent!==worldRoot&&parent.children.length===0&&parent.parent)parent.parent.remove(parent);}
  for(const geometry of geometries)geometry.dispose();
 }
 staticBoxCandidates.length=0;
}
function initDustPool(){
 dustDummy=new THREE.Object3D();const geometry=new THREE.IcosahedronGeometry(1,0);const material=new THREE.MeshBasicMaterial({color:0xc7bba5,transparent:true,opacity:.42,depthWrite:false,toneMapped:false});
 dustMesh=new THREE.InstancedMesh(geometry,material,MAX_DUST);dustMesh.name='PooledSlideDust';dustMesh.frustumCulled=false;dustMesh.castShadow=false;dustMesh.receiveShadow=false;dustMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
 dustParticles=Array.from({length:MAX_DUST},()=>({active:false,pos:new THREE.Vector3(),vel:new THREE.Vector3(),life:0,maxLife:.35,size:.1}));
 for(let i=0;i<MAX_DUST;i++){dustDummy.position.set(0,-1000,0);dustDummy.scale.setScalar(0);dustDummy.updateMatrix();dustMesh.setMatrixAt(i,dustDummy.matrix);}dustMesh.instanceMatrix.needsUpdate=true;worldRoot.add(dustMesh);
}
function v3mat(color){return mat(color,.95,0);}
// ===================== VILLAGE DETAIL PASS (v63) =====================
// Richer ground (grass + cobbled streets), building facades (plinth, shutters, flower boxes, banners, lanterns, steps),
// district courtyards (wells, fountains, sakura, benches, market stalls, string lanterns) and a planted outer ring.
// Tweak: DETAIL.density (0..2) scales the amount of grass / flowers / rocks / bushes scattered on the ground.
const DETAIL={density:1};
let _dseed=20261102;function drand(){_dseed=(_dseed*1664525+1013904223)>>>0;return _dseed/4294967296;}
const DET={tufts:[],flowers:[],pebbles:[],rocks:[],bushes:[],barrels:[]};
let texGrass,texCobble,texStoneG,texPlasterG;
// BoxGeometry UVs run 0..1 per face; scale them to metres so textures keep a constant size on any box.
function tileBoxUV(geo,w,h,d,ts){
 const uv=geo.attributes.uv,sz=[[d,h],[d,h],[w,d],[w,d],[w,h],[w,h]];   // faces: +x -x +y -y +z -z
 for(let f=0;f<6;f++)for(let i=0;i<4;i++){const k=f*4+i;uv.setXY(k,uv.getX(k)*sz[f][0]/ts,uv.getY(k)*sz[f][1]/ts);}
 uv.needsUpdate=true;return geo;
}
function paveBox(w,d,material,x,y,z,ts=5,hgt=.08){
 const g=new THREE.BoxGeometry(w,hgt,d);tileBoxUV(g,w,hgt,d,ts);
 const m=new THREE.Mesh(g,material);m.position.set(x,y,z);m.receiveShadow=true;worldRoot.add(m);staticBoxCandidates.push(m);return m;
}
function makeDetailMats(){
 texGrass=canvasTexture('grass');texGrass.repeat.set(72,72);
 texCobble=canvasTexture('cobble');
 texStoneG=texStone.clone();texStoneG.repeat.set(1/6,1/6);texStoneG.needsUpdate=true;
 texPlasterG=texPlaster.clone();texPlasterG.repeat.set(1/6,1/6);texPlasterG.needsUpdate=true;
 Object.assign(mats,{
  grass:new THREE.MeshStandardMaterial({map:texGrass,color:0xffffff,roughness:1}),
  cobble:new THREE.MeshStandardMaterial({map:texCobble,color:0xd9d3c4,roughness:1}),
  cobble2:new THREE.MeshStandardMaterial({map:texCobble,color:0xc3c7bd,roughness:1}),
  wallStone:new THREE.MeshStandardMaterial({map:texStone,color:0x9b9a92,roughness:1}),
  stoneDark:mat(0x6a6a64,.95),iron:mat(0x2b2d30,.55,.6),rut:mat(0x8a8576,1),
  shutterA:mat(0x5b3a2a),shutterB:mat(0x3f5a4b),shutterC:mat(0x2e4258),
  shutterD:mat(0x76503c),shutterE:mat(0x485c70),shutterF:mat(0x66714b),
  windowBlue:new THREE.MeshStandardMaterial({color:0x314957,roughness:.24,metalness:.18}),
  windowWarm:new THREE.MeshStandardMaterial({color:0x554637,emissive:0x6c3c17,emissiveIntensity:.12,roughness:.3}),
  windowGreen:new THREE.MeshStandardMaterial({color:0x334d47,roughness:.26,metalness:.12}),
  windowFrameA:mat(0x59402d),windowFrameB:mat(0x344e5d),windowFrameC:mat(0x806044),windowFrameD:mat(0x6b6b5a),
  planter:mat(0x57402c),soil:mat(0x33261b),plant:mat(0x4d7c3b),plant2:mat(0x69944a),
  fl1:mat(0xd8506f),fl2:mat(0xf1d24a),fl3:mat(0xece8f2),fl4:mat(0x8a6fd0),
  clothRed:mat(0xa83a32),clothCream:mat(0xe4d9bb),clothIndigo:mat(0x2d4766),clothGreen:mat(0x59773f),
  hay:mat(0xc3a14d),sack:mat(0xb59f74),
  water:new THREE.MeshStandardMaterial({color:0x3e7389,roughness:.12,metalness:.35,transparent:true,opacity:.85}),
  blossom:mat(0xf0b4c8),blossom2:mat(0xe598b3),petals:new THREE.MeshBasicMaterial({color:0xf3c2d2,transparent:true,opacity:.5,depthWrite:false})
 });
}
function propCollider(x,z,w,d,top){addCollider(x,z,w,d,top,'prop');}
// ---------- small props ----------
function propCrateStack(x,z,n=2){
 const s=1.05;
 boxMesh(s,s,s,mats.wood,x,s/2,z);boxMesh(s+.05,.1,s+.05,mats.darkWood,x,s*.18,z);boxMesh(s+.05,.1,s+.05,mats.darkWood,x,s*.82,z);
 let top=s;
 if(n>1){const s2=.8;boxMesh(s2,s2,s2,mats.wood,x+.08,s+s2/2,z-.05);boxMesh(s2+.05,.09,s2+.05,mats.darkWood,x+.08,s+s2*.2,z-.05);top=s+s2;}
 boxMesh(.9,.7,.9,mats.wood,x+1.0,.35,z+.25);boxMesh(.95,.08,.95,mats.darkWood,x+1.0,.72,z+.25);
 boxMesh(.8,.5,.55,mats.sack,x-.9,.25,z+.4);
 propCollider(x,z,s,s,top);propCollider(x+1.0,z+.25,.9,.9,.72);
}
function propBarrel(x,z,s=1){DET.barrels.push(x,z,s);propCollider(x,z,.95*s,.95*s,1.15*s);}
function propPot(x,y,z){boxMesh(.5,.5,.5,mats.planter,x,y+.25,z);const fi=Math.floor(drand()*3);   // (drand is called exactly once, as before, so the world layout does not change)
 if(VEG.enabled){try{vegAddBush(worldRoot,x,y+.46,z,.62,fi*2.1,[.3,.5,.22],'pot');vegAddFlowers(worldRoot,x,y+1.0,z,fi);return;}catch(err){console.warn('Potted plant v2 failed:',err);VEG.enabled=false;}}
 boxMesh(.62,.66,.62,mats.plant,x,y+.8,z);boxMesh(.2,.2,.2,[mats.fl1,mats.fl2,mats.fl3][fi],x,y+1.2,z);}
function propBench(x,z,rot){
 const g=new THREE.Group();g.position.set(x,0,z);g.rotation.y=rot;worldRoot.add(g);
 boxMesh(2.3,.14,.7,mats.wood,0,.5,0,g);boxMesh(2.3,.55,.1,mats.wood,0,.9,-.33,g);
 for(const sx of [-1,1]){boxMesh(.14,.5,.62,mats.darkWood,sx*.95,.25,0,g);}
 const alongX=Math.abs(Math.sin(rot))<.5;propCollider(x,z,alongX?2.3:.8,alongX?.8:2.3,.55);
}
function lanternAt(x,y,z){lanternGlowData.push({x,y,z});}
// market stall: front faces local +z, rot must be a multiple of PI/2
function propStall(x,z,rot,cloth){
 const g=new THREE.Group();g.position.set(x,0,z);g.rotation.y=rot;worldRoot.add(g);
 const c=Math.cos(rot),s=Math.sin(rot),W=(lx,lz)=>[x+lx*c+lz*s,z-lx*s+lz*c];
 for(const sx of [-1,1])for(const sz of [-1,1])boxMesh(.14,2.7,.14,mats.darkWood,sx*1.5,1.35,sz*.95,g);
 const canopy=boxMesh(3.5,.1,2.5,mats.clothCream,0,2.75,0,g);canopy.rotation.x=-.12;
 for(let i=0;i<4;i++){const st=boxMesh(.44,.11,2.52,cloth,-1.31+i*.875,2.755,0,g);st.rotation.x=-.12;}
 for(let i=0;i<8;i++)boxMesh(.4,.32,.05,i%2?cloth:mats.clothCream,-1.5+i*.43,2.5,1.2,g);
 boxMesh(3.0,.9,.8,mats.wood,0,.45,.75,g);boxMesh(3.2,.09,1.0,mats.darkWood,0,.94,.75,g);
 boxMesh(3.0,1.7,.12,mats.darkWood,0,1.0,-.9,g);boxMesh(2.8,.08,.5,mats.wood,0,1.35,-.65,g);
 const goods=[mats.fl1,mats.fl2,mats.plant2,mats.hay,mats.clothRed];
 for(let i=0;i<5;i++){boxMesh(.46,.22,.46,mats.planter,-1.1+i*.55,1.1,.75,g);boxMesh(.38,.14,.38,goods[(i+Math.floor(drand()*3))%5],-1.1+i*.55,1.25,.75,g);}
 boxMesh(.6,.5,.6,mats.wood,1.85,.25,.2,g);boxMesh(.55,.45,.5,mats.sack,-1.9,.22,.3,g);
 for(const sx of [-1,1]){const p=W(sx*1.4,1.0);lanternAt(p[0],2.3,p[1]);}
 const cp=W(0,.75),alongX=Math.abs(s)<.5;propCollider(cp[0],cp[1],alongX?3.0:.9,alongX?.9:3.0,.96);
}
function propWell(cx,cz){
 boxMesh(3.4,1.0,.75,mats.stone,cx,.5,cz-1.33);boxMesh(3.4,1.0,.75,mats.stone,cx,.5,cz+1.33);
 boxMesh(.75,1.0,1.9,mats.stone,cx-1.33,.5,cz);boxMesh(.75,1.0,1.9,mats.stone,cx+1.33,.5,cz);
 boxMesh(3.6,.14,3.6,mats.stoneDark,cx,1.03,cz);boxMesh(1.9,.05,1.9,mats.water,cx,.7,cz);
 for(const sx of [-1,1])boxMesh(.28,3.3,.28,mats.darkWood,cx+sx*1.55,1.65,cz);
 boxMesh(.2,.2,3.2,mats.darkWood,cx,3.0,cz);boxMesh(.2,.5,.2,mats.wood,cx,2.6,cz);
 for(const sx of [-1,1]){const r=boxMesh(2.6,.2,3.0,mats.roof,cx+sx*.95,3.55,cz);r.rotation.z=-sx*.5;}
 boxMesh(.5,.28,3.2,mats.darkWood,cx,4.15,cz);
 for(let i=0;i<6;i++)boxMesh(.9,.35,.7,mats.stone,cx+Math.cos(i*1.05)*3.2,.17,cz+Math.sin(i*1.05)*3.2);
 propCollider(cx,cz,3.4,3.4,1.1);
}
function propFountain(cx,cz){
 const stone=mats.stone,rim=new THREE.Mesh(new THREE.CylinderGeometry(3.5,3.7,.8,28),stone);rim.position.set(cx,.4,cz);worldRoot.add(rim);
 const water=new THREE.Mesh(new THREE.CylinderGeometry(3.15,3.15,.1,28),mats.water);water.position.set(cx,.72,cz);worldRoot.add(water);
 const col=new THREE.Mesh(new THREE.CylinderGeometry(.35,.55,2.2,10),stone);col.position.set(cx,1.5,cz);worldRoot.add(col);
 const bowl=new THREE.Mesh(new THREE.CylinderGeometry(1.4,.8,.45,16),stone);bowl.position.set(cx,2.45,cz);worldRoot.add(bowl);
 const w2=new THREE.Mesh(new THREE.CylinderGeometry(1.2,1.2,.08,16),mats.water);w2.position.set(cx,2.7,cz);worldRoot.add(w2);
 const top=new THREE.Mesh(new THREE.SphereGeometry(.42,10,8),stone);top.position.set(cx,3.1,cz);worldRoot.add(top);
 for(const m of [rim,water,col,bowl,w2,top]){m.receiveShadow=true;}
 {const n0=colliders.length;propCollider(cx,cz,6.2,3.2,2.6);propCollider(cx,cz,3.2,6.2,2.6);propCollider(cx,cz,5.0,5.0,2.6);   // taller than any jump, and flagged: no mantle / fast-climb / wall-run / standing on it
  for(let i=n0;i<colliders.length;i++){colliders[i].noClimb=true;colliders[i].noStand=true;}}
}
function propSakura(cx,cz){
 const g=new THREE.Group();g.position.set(cx,0,cz);worldRoot.add(g);
 let sakV2=false;if(VEG.enabled){try{vegAddTree(g,'sakura',0,0,0,0,1);sakV2=true;}catch(err){console.warn('Sakura v2 failed; using the old tree:',err);VEG.enabled=false;}}
 if(!sakV2){
 const trunk=new THREE.Mesh(new THREE.CylinderGeometry(.35,.62,4.4,8),mats.treeTrunk);trunk.position.y=2.2;g.add(trunk);
 for(const [bx,by,bz,r] of [[0,6,0,2.9],[1.9,5.3,.6,2.2],[-1.8,5.5,-.5,2.3],[.4,5.2,-1.9,2.1],[-.5,5.0,1.9,2.0],[0,7.3,.2,1.9]]){
  const m=new THREE.Mesh(new THREE.IcosahedronGeometry(r,1),(bx+bz)>0?mats.blossom:mats.blossom2);m.position.set(bx,by,bz);m.scale.set(1,.8,1);g.add(m);}
 const br=new THREE.Mesh(new THREE.CylinderGeometry(.14,.22,2.4,5),mats.treeTrunk);br.position.set(1.0,4.6,.3);br.rotation.z=-.7;g.add(br);
 }
 const pet=new THREE.Mesh(new THREE.CircleGeometry(5.2,24),mats.petals);pet.rotation.x=-Math.PI/2;pet.position.y=.1;pet.name='PetalDecal';g.add(pet);
 // stone lantern beside the tree
 const lx=cx+4.6,lz=cz+1.2;
 boxMesh(1.1,.28,1.1,mats.stone,lx,.14,lz);boxMesh(.42,1.0,.42,mats.stoneDark,lx,.78,lz);boxMesh(.9,.18,.9,mats.stone,lx,1.35,lz);
 boxMesh(.7,.62,.7,mats.stoneDark,lx,1.75,lz);lanternAt(lx,1.75,lz);boxMesh(1.35,.22,1.35,mats.stone,lx,2.17,lz);boxMesh(.5,.3,.5,mats.stone,lx,2.43,lz);
 propCollider(cx,cz,1.0,1.0,.4);
}
function ropeLanterns(x1,z1,x2,z2,y,n){
 const dx=x2-x1,dz=z2-z1,len=Math.hypot(dx,dz);
 if(Math.abs(dx)>=Math.abs(dz))boxMesh(len,.06,.06,mats.rope,(x1+x2)/2,y,(z1+z2)/2);else boxMesh(.06,.06,len,mats.rope,(x1+x2)/2,y,(z1+z2)/2);
 for(let i=1;i<=n;i++){const t=i/(n+1),sag=Math.sin(t*Math.PI)*.35,px=x1+dx*t,pz=z1+dz*t;boxMesh(.03,.5,.03,mats.rope,px,y-.25-sag,pz);lanternAt(px,y-.7-sag,pz);}
}
// ---------- building facades ----------
function addWindowDetail(xx,yy,faceZ,face,variant,j){
 const type=variant%5;
 const shutters=[mats.shutterA,mats.shutterB,mats.shutterC,mats.shutterD,mats.shutterE,mats.shutterF];
 const frame=[mats.windowFrameA,mats.windowFrameB,mats.windowFrameC,mats.windowFrameD][(variant+j)%4];
 const sm=shutters[(variant*2+j)%shutters.length],zz=faceZ+face*.105;
 const bar=(w,h,d,x,y,z,material=frame)=>boxMesh(w,h,d,material,x,y,z);
 if(type===0){
  // Japanese timber window with two side shutters and a strong lintel.
  bar(.13,1.58,.18,xx-.67,yy,zz);bar(.13,1.58,.18,xx+.67,yy,zz);
  bar(1.42,.13,.18,xx,yy+.78,zz);bar(1.42,.12,.18,xx,yy-.78,zz);
  bar(.08,1.36,.17,xx,yy,zz+.015,mats.wood);
  bar(.48,1.45,.1,xx-.91,yy,zz-.03,sm);bar(.48,1.45,.1,xx+.91,yy,zz-.03,sm);
 }else if(type===1){
  // Tall, narrow vertical windows with paired side columns and two transoms.
  bar(.13,1.96,.2,xx-.49,yy,zz);bar(.13,1.96,.2,xx+.49,yy,zz);
  bar(.98,.14,.2,xx,yy+.96,zz);bar(.98,.14,.2,xx,yy-.96,zz);
  bar(.84,.09,.18,xx,yy+.28,zz+.015,mats.wood);bar(.84,.09,.18,xx,yy-.34,zz+.015,mats.wood);
  bar(.24,1.78,.11,xx-.69,yy,zz-.035,sm);bar(.24,1.78,.11,xx+.69,yy,zz-.035,sm);
 }else if(type===2){
  // Broad horizontal shop-house window with a projecting sun hood and vertical mullions.
  bar(1.98,.14,.22,xx,yy+.57,zz);bar(1.98,.14,.22,xx,yy-.57,zz);
  bar(.14,1.05,.22,xx-.95,yy,zz);bar(.14,1.05,.22,xx+.95,yy,zz);
  for(const q of [-.32,.32])bar(.08,.94,.18,xx+q,yy,zz+.02,mats.wood);
  bar(2.25,.13,.62,xx,yy+.83,zz-.12,sm);
  for(let q=-2;q<=2;q++)bar(.08,.18,.12,xx+q*.42,yy+.94,zz-.12,frame);
 }else if(type===3){
  // Squared four-light window with cross muntins and a stone sill.
  bar(1.38,.15,.2,xx,yy+.68,zz);bar(1.38,.15,.2,xx,yy-.68,zz);
  bar(.15,1.38,.2,xx-.62,yy,zz);bar(.15,1.38,.2,xx+.62,yy,zz);
  bar(.08,1.18,.17,xx,yy,zz+.02,mats.wood);bar(1.18,.08,.17,xx,yy,zz+.02,mats.wood);
  bar(1.52,.12,.32,xx,yy-.82,zz+.04,mats.stone);
 }else{
  // Arched upper window with a curved stone surround and narrow side shutters.
  bar(.14,1.28,.2,xx-.69,yy-.18,zz);bar(.14,1.28,.2,xx+.69,yy-.18,zz);
  bar(1.38,.14,.2,xx,yy-.84,zz);
  const pts=[
   new THREE.Vector3(xx-.69,yy+.44,zz),
   new THREE.Vector3(xx-.62,yy+.78,zz),
   new THREE.Vector3(xx-.34,yy+.98,zz),
   new THREE.Vector3(xx,yy+1.05,zz),
   new THREE.Vector3(xx+.34,yy+.98,zz),
   new THREE.Vector3(xx+.62,yy+.78,zz),
   new THREE.Vector3(xx+.69,yy+.44,zz)
  ];
  const arch=new THREE.Mesh(new THREE.TubeGeometry(new THREE.CatmullRomCurve3(pts),20,.075,6,false),mats.stone);arch.castShadow=true;arch.receiveShadow=true;worldRoot.add(arch);
  bar(.08,1.12,.16,xx,yy-.18,zz+.02,mats.wood);
  bar(.26,1.22,.1,xx-.9,yy-.18,zz-.04,sm);bar(.26,1.22,.1,xx+.9,yy-.18,zz-.04,sm);
 }
 if(type!==3)bar(1.5,.12,.28,xx,yy-.88,faceZ+face*.18,mats.stone);
 if(yy<4.5&&(j+variant)%2===0){
  bar(1.45,.3,.4,xx,yy-1.02,faceZ+face*.3,mats.planter);
  bar(1.35,.18,.34,xx,yy-.82,faceZ+face*.3,mats.plant);
  for(let q=0;q<4;q++)bar(.14,.14,.14,xx-.5+q*.34,yy-.68,faceZ+face*.3,[mats.fl1,mats.fl2,mats.fl3,mats.fl4][(q+j)%4]);
 }
}
function buildingDetails(x,z,w,d,h,variant,index,dist,roofRise,roofD,roofMat,openRoof=false){
 // stone plinth around the base
 boxMesh(w+.5,.75,d+.5,mats.stoneDark,x,.375,z);boxMesh(w+.62,.12,d+.62,mats.stone,x,.8,z);
 // ground-level entrance with steps, noren curtain and lanterns (front = -z)
 const fz=z-d/2;
 boxMesh(3.4,3.3,.3,mats.darkWood,x,1.65,fz-.38);boxMesh(2.5,2.85,.32,mats.door,x,1.45,fz-.4);
 boxMesh(3.7,.28,.7,mats.darkWood,x,3.45,fz-.55);
 const nc=[mats.clothIndigo,mats.clothRed,mats.clothCream][variant%3];
 for(let i=0;i<4;i++){boxMesh(.58,1.0,.05,nc,x-.95+i*.64,2.85,fz-.62);}
 boxMesh(3.4,.18,.9,mats.stoneDark,x,.09,fz-1.05);boxMesh(3.0,.3,.55,mats.stone,x,.15,fz-.75);
 for(const sx of [-1,1]){boxMesh(.12,2.4,.12,mats.darkWood,x+sx*2.2,1.2,fz-.7);lanternAt(x+sx*2.2,2.55,fz-.7);propPot(x+sx*3.0,0,fz-1.0);}
 // banners on the front and back facade
 const bc=[mats.clothRed,mats.clothIndigo,mats.clothCream,mats.clothGreen][(index+variant)%4];
 for(const face of [-1,1])for(const sx of [-1,1]){
  const bx=x+sx*(w*.5-1.1),bz=z+face*(d/2+.2),by=Math.min(h*.62,14);
  boxMesh(1.0,.1,.12,mats.darkWood,bx,by+1.6,bz);boxMesh(.9,3.0,.05,bc,bx,by,bz+face*.06);boxMesh(.9,.18,.07,mats.clothCream,bx,by-1.3,bz+face*.07);
 }
 // wall brackets with hanging lanterns along the front
 const nL=Math.max(2,Math.floor(w/6));
 for(let i=0;i<nL;i++){const lx=x-w*.36+i*(w*.72/Math.max(1,nL-1));if(Math.abs(lx-x)<2.6)continue;boxMesh(.12,.12,1.0,mats.darkWood,lx,4.1,fz-.55);boxMesh(.03,.4,.03,mats.rope,lx,3.85,fz-1.0);lanternAt(lx,3.35,fz-1.0);}
 // Ridge finials belong only to traditional pitched roofs.
 if(!openRoof)for(const sz of [-1,1]){boxMesh(.8,1.1,.6,roofMat,x,h+roofRise+.7,z+sz*(roofD/2-.45));boxMesh(.35,.6,.35,mats.darkWood,x,h+roofRise+1.5,z+sz*(roofD/2-.45));}
 // barrels / crates against the wall (small cluster per building)
 const side=(index%2===0)?1:-1;
 propCrateStack(x+side*w*.3,fz-1.5,index%3===0?2:1);
 propBarrel(x-side*w*.3,fz-1.2,1);propBarrel(x-side*w*.3+1.05,fz-1.35,.85);
}
// ---------- district courtyard ----------
function buildDistrictDetails(index,cx,cz){
 const kind=index%3;
 if(kind===0)propWell(cx,cz);else if(kind===1)propFountain(cx,cz);else propSakura(cx,cz);
 propBench(cx,cz-6.6,0);propBench(cx,cz+6.6,Math.PI);
 if(kind===2){propBench(cx-6.6,cz,Math.PI/2);propBench(cx+6.6,cz,-Math.PI/2);}
 const cl=[mats.clothRed,mats.clothIndigo,mats.clothGreen,mats.clothRed,mats.clothIndigo,mats.clothGreen];
 propStall(cx-9.2,cz-23,Math.PI/2,cl[index]);propStall(cx+9.2,cz+23,-Math.PI/2,cl[(index+1)%6]);
 propStall(cx-23,cz+9.2,Math.PI,cl[(index+2)%6]);propStall(cx+23,cz-9.2,0,cl[(index+3)%6]);
 // string lanterns across the two alleys
 ropeLanterns(cx-11.2,cz-22,cx+11.2,cz-22,7.2,7);ropeLanterns(cx-22,cz-11.2,cx-22,cz+11.2,7.2,7);
 // hedges and flowers along the district edge (gaps left where the alleys open)
 for(let t=-36;t<=36;t+=3.4){
  if(Math.abs(t)<14)continue;
  for(const e of [-37.2,37.2]){
   DET.bushes.push(cx+e,cz+t+(drand()-.5)*.8,.9+drand()*.7,drand());DET.bushes.push(cx+t+(drand()-.5)*.8,cz+e,.9+drand()*.7,drand());
   if(drand()<.55){DET.flowers.push(cx+e+(drand()-.5)*2,cz+t,drand());DET.flowers.push(cx+t,cz+e+(drand()-.5)*2,drand());}
  }
 }
 // paving details: drain grates and a scatter of pebbles
 for(const gx of [-13,13])for(const gz of [-13,13])boxMesh(.9,.04,.5,mats.iron,cx+gx,.1,cz+gz);
 for(let i=0;i<46;i++){const px=cx+(drand()-.5)*74,pz=cz+(drand()-.5)*74;DET.pebbles.push(px,pz,.5+drand()*.8,drand()*6.28,drand());}
}
function buildStreetDetails(){
 // stone curbs along the two main streets (outside the district footprints)
 for(const sz of [-1,1])for(const sx of [-1,1])boxMesh(127.4,.2,.36,mats.stoneDark,sx*76.3,.1,sz*12.7);
 for(const sx of [-1,1])for(const sz of [-1,1]){boxMesh(.36,.2,8.4,mats.stoneDark,sx*12.7,.1,sz*16.8);boxMesh(.36,.2,21,mats.stoneDark,sx*12.7,.1,sz*109.5);}
 // wheel ruts and drains
 for(const rz of [-3.2,3.2])boxMesh(270,.02,.55,mats.rut,-1,.055,rz);
 for(const rx of [-3.2,3.2])boxMesh(.55,.02,230,mats.rut,rx,.065,0);
 for(let x=-130;x<=130;x+=26){if(Math.abs(x)<16)continue;for(const sz of [-1,1])boxMesh(1.0,.04,.5,mats.iron,x,.09,sz*11.6);}
 // plaza: stone rings, central fountain
 for(const r of [11.3,7.8]){const ring=new THREE.Mesh(new THREE.RingGeometry(r-.22,r+.22,64),mats.pathLine);ring.rotation.x=-Math.PI/2;ring.position.set(0,.06,0);worldRoot.add(ring);}
 for(let i=0;i<8;i++){const a=i/8*Math.PI*2;boxMesh(.7,.5,.7,mats.stone,Math.cos(a)*10.4,.25,Math.sin(a)*10.4);}
 // (central fountain removed: the captive stands at the plaza centre instead)
}
function freeGround(x,z,pad=0){
 if(Math.abs(z)<15+pad&&Math.abs(x)<144)return false;
 if(Math.abs(x)<15+pad&&Math.abs(z)<124)return false;
 if(Math.abs(x)<131+pad&&Math.abs(z)<103+pad)return false;
 return Math.hypot(x,z)<WORLD.wallRadius-9;
}
function scatterGround(){
 const dn=DETAIL.density,R=WORLD.wallRadius-10;
 for(let c=0,n=Math.round(900*dn);c<n;c++){
  const a=drand()*Math.PI*2,r=Math.sqrt(drand())*R,x=Math.cos(a)*r,z=Math.sin(a)*r;if(!freeGround(x,z))continue;
  const k=5+Math.floor(drand()*6);
  for(let i=0;i<k;i++){const px=x+(drand()-.5)*7,pz=z+(drand()-.5)*7;if(freeGround(px,pz))DET.tufts.push(px,pz,.7+drand()*.9,drand()*6.28,drand());}
  if(drand()<.3){const m=3+Math.floor(drand()*4);for(let i=0;i<m;i++){const px=x+(drand()-.5)*4,pz=z+(drand()-.5)*4;if(freeGround(px,pz))DET.flowers.push(px,pz,drand());}}
  if(drand()<.25){const m=3+Math.floor(drand()*5);for(let i=0;i<m;i++){const px=x+(drand()-.5)*4,pz=z+(drand()-.5)*4;if(freeGround(px,pz))DET.pebbles.push(px,pz,.5+drand()*.9,drand()*6.28,drand());}}
 }
 for(let i=0,n=Math.round(130*dn);i<n;i++){const a=drand()*Math.PI*2,r=Math.sqrt(drand())*R,x=Math.cos(a)*r,z=Math.sin(a)*r;if(freeGround(x,z,2))DET.rocks.push(x,z,.5+drand()*1.4,drand()*6.28,drand());}
 for(let i=0,n=Math.round(150*dn);i<n;i++){const a=drand()*Math.PI*2,r=Math.sqrt(drand())*R,x=Math.cos(a)*r,z=Math.sin(a)*r;if(freeGround(x,z,2))DET.bushes.push(x,z,.9+drand()*.9,drand());}
 // a ring of bushes against the foot of the outer wall
 for(let i=0;i<110;i++){const a=i/110*Math.PI*2+drand()*.02,r=WORLD.wallRadius-6.2-drand()*1.5;DET.bushes.push(Math.cos(a)*r,Math.sin(a)*r,1+drand()*.8,drand());}
 // extra trees in the open ground
 let made=0;for(let tries=0;tries<400&&made<26;tries++){const a=drand()*Math.PI*2,r=Math.sqrt(drand())*(R-6),x=Math.cos(a)*r,z=Math.sin(a)*r;if(!freeGround(x,z,5))continue;makeTree(x,z,drand()<.5);made++;}
}
function buildDetailInstances(){
 scatterGround();
 const dummy=new THREE.Object3D(),col=new THREE.Color();
 const mk=(geo,material,n,name)=>{const m=new THREE.InstancedMesh(geo,material,Math.max(1,n));m.name=name;m.castShadow=false;m.receiveShadow=false;m.instanceMatrix.setUsage(THREE.StaticDrawUsage);m.count=n;return m;};
 const fin=(m)=>{m.instanceMatrix.needsUpdate=true;if(m.instanceColor)m.instanceColor.needsUpdate=true;m.computeBoundingBox();m.computeBoundingSphere();worldRoot.add(m);};
 // grass tufts
 {const n=DET.tufts.length/5;let geo,tmat,tv2=false;if(VEG.enabled){try{geo=vegGeo(vegBuildTuft());tmat=vegMats().grass;tv2=true;}catch(err){console.warn('Grass v2 failed:',err);VEG.enabled=false;}}
  if(!tv2){geo=new THREE.ConeGeometry(.08,.7,4,1);geo.translate(0,.35,0);tmat=new THREE.MeshStandardMaterial({color:0xffffff,roughness:1});}
  const m=mk(geo,tmat,n,'GrassTufts'),gk=tv2?1.7:1;
  const pal=[0x5f8a45,0x6f9a4c,0x4d7a3c,0x86a255,0x7a8a46];
  for(let i=0;i<n;i++){const o=i*5;dummy.position.set(DET.tufts[o],0,DET.tufts[o+1]);const s=DET.tufts[o+2];dummy.scale.set(s,s*(.8+DET.tufts[o+4]*.7),s);dummy.rotation.set((DET.tufts[o+4]-.5)*.5,DET.tufts[o+3],(DET.tufts[o+4]-.5)*.4);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);col.setHex(pal[Math.floor(DET.tufts[o+4]*pal.length)%pal.length]).multiplyScalar(gk);m.setColorAt(i,col);}
  if(n)fin(m);}
 // flowers
 {const n=DET.flowers.length/3;let geo,fmat,fv2=false;if(VEG.enabled){try{geo=vegGeo(vegBuildFlower());fmat=vegMats().flower;fv2=true;}catch(err){console.warn('Flowers v2 failed:',err);VEG.enabled=false;}}
  if(!fv2){geo=new THREE.SphereGeometry(.13,6,5);fmat=new THREE.MeshStandardMaterial({color:0xffffff,roughness:.7});}
  const m=mk(geo,fmat,n,'Flowers');
  const pal=[0xd8506f,0xf1d24a,0xece8f2,0x8a6fd0,0xf08a3c];
  for(let i=0;i<n;i++){const o=i*3;dummy.position.set(DET.flowers[o],.55+DET.flowers[o+2]*.2,DET.flowers[o+1]);dummy.scale.setScalar(.8+DET.flowers[o+2]*.6);dummy.rotation.set(0,fv2?DET.flowers[o+2]*37:0,0);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);col.setHex(pal[Math.floor(DET.flowers[o+2]*pal.length)%pal.length]);m.setColorAt(i,col);}
  if(n){fin(m);
   // short stems so the blossoms do not float
   const sg=new THREE.CylinderGeometry(.015,.015,.6,3);sg.translate(0,.3,0);const sm=mk(sg,new THREE.MeshStandardMaterial({color:0x4d7a3c,roughness:1}),n,'FlowerStems');
   for(let i=0;i<n;i++){const o=i*3;dummy.position.set(DET.flowers[o],0,DET.flowers[o+1]);dummy.scale.set(1,1+DET.flowers[o+2]*.35,1);dummy.rotation.set(0,0,0);dummy.updateMatrix();sm.setMatrixAt(i,dummy.matrix);}
   fin(sm);}}
 // pebbles
 {const n=DET.pebbles.length/5,geo=new THREE.IcosahedronGeometry(.16,0);const m=mk(geo,new THREE.MeshStandardMaterial({color:0xffffff,roughness:1,flatShading:true}),n,'Pebbles');
  const pal=[0x8b8a82,0x77766f,0xa09b8c,0x6a6a66,0x948d7d];
  for(let i=0;i<n;i++){const o=i*5,s=DET.pebbles[o+2];dummy.position.set(DET.pebbles[o],.05,DET.pebbles[o+1]);dummy.scale.set(s,s*.55,s*(.8+DET.pebbles[o+4]*.4));dummy.rotation.set(0,DET.pebbles[o+3],0);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);col.setHex(pal[Math.floor(DET.pebbles[o+4]*pal.length)%pal.length]);m.setColorAt(i,col);}
  if(n)fin(m);}
 // boulders
 {const n=DET.rocks.length/5,geo=new THREE.IcosahedronGeometry(1,0);const m=mk(geo,new THREE.MeshStandardMaterial({color:0xffffff,roughness:1,flatShading:true}),n,'Rocks');
  const pal=[0x7d7c75,0x6b6b66,0x8e8a7e,0x5f605d];
  for(let i=0;i<n;i++){const o=i*5,s=DET.rocks[o+2];dummy.position.set(DET.rocks[o],s*.3,DET.rocks[o+1]);dummy.scale.set(s,s*.62,s*(.8+DET.rocks[o+4]*.5));dummy.rotation.set(DET.rocks[o+4]*.4,DET.rocks[o+3],0);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);col.setHex(pal[Math.floor(DET.rocks[o+4]*pal.length)%pal.length]);m.setColorAt(i,col);}
  if(n)fin(m);}
 // bushes
 {const n=DET.bushes.length/4;let bv=null;
  if(VEG.enabled){try{const B=vegBuildBush(),M=vegMats();bv={leaf:mk(vegGeo(B.leaf),M.leaf,n,'Bushes'),core:mk(vegGeo(B.core),M.core,n,'Bushes')};}catch(err){console.warn('Bushes v2 failed:',err);VEG.enabled=false;bv=null;}}
  const m=bv?bv.leaf:mk(new THREE.IcosahedronGeometry(.9,1),new THREE.MeshStandardMaterial({color:0xffffff,roughness:1,flatShading:true}),n,'Bushes'),gk=bv?2.0:1;
  const pal=[0x3f6a3c,0x4f7a43,0x365f3a,0x5b8548,0x6a8a45];
  for(let i=0;i<n;i++){const o=i*4,s=DET.bushes[o+2];dummy.position.set(DET.bushes[o],bv?0:s*.5,DET.bushes[o+1]);dummy.scale.set(s,s*(bv?1.05:.8),s*(.9+DET.bushes[o+3]*.3));dummy.rotation.set(0,DET.bushes[o+3]*6.28,0);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);col.setHex(pal[Math.floor(DET.bushes[o+3]*pal.length)%pal.length]).multiplyScalar(gk);m.setColorAt(i,col);if(bv){bv.core.setMatrixAt(i,dummy.matrix);bv.core.setColorAt(i,col);}}
  if(n){fin(m);if(bv)fin(bv.core);}}
 // barrels
 {const n=DET.barrels.length/3,geo=new THREE.CylinderGeometry(.42,.38,1.1,10);geo.translate(0,.55,0);const m=mk(geo,mats.wood,n,'Barrels');
  for(let i=0;i<n;i++){const o=i*3,s=DET.barrels[o+2];dummy.position.set(DET.barrels[o],0,DET.barrels[o+1]);dummy.scale.set(s,s,s);dummy.rotation.set(0,i*1.7,0);dummy.updateMatrix();m.setMatrixAt(i,dummy.matrix);}
  if(n){fin(m);
   const bg=new THREE.CylinderGeometry(.435,.435,.07,10),bm=mk(bg,mats.iron,n*2,'BarrelHoops');let k=0;
   for(let i=0;i<n;i++){const o=i*3,s=DET.barrels[o+2];for(const hy of [.28,.82]){dummy.position.set(DET.barrels[o],hy*s,DET.barrels[o+1]);dummy.scale.set(s,s,s);dummy.rotation.set(0,0,0);dummy.updateMatrix();bm.setMatrixAt(k++,dummy.matrix);}}
   fin(bm);}}
}

function buildWorld(){texStone=canvasTexture('stone');texPlaster=canvasTexture('plaster');texRoof=canvasTexture('roof');
 mats.stone=new THREE.MeshStandardMaterial({map:texStone,color:0xc2c0b7,roughness:1});mats.plaster=new THREE.MeshStandardMaterial({map:texPlaster,color:0xd7c7a7,roughness:1});mats.plasterLight=new THREE.MeshStandardMaterial({map:texPlaster,color:0xe1d9c6,roughness:1});mats.plasterWarm=new THREE.MeshStandardMaterial({map:texPlaster,color:0xd1ad7b,roughness:1});mats.roof=new THREE.MeshStandardMaterial({map:texRoof,color:0xb96c4d,roughness:.93});mats.roof2=new THREE.MeshStandardMaterial({map:texRoof,color:0x5b6f76,roughness:.92});mats.roof3=new THREE.MeshStandardMaterial({map:texRoof,color:0x837c5e,roughness:.95});
 Object.assign(mats,{wood:mat(0x65452e),darkWood:mat(0x342b27),door:mat(0x493128),window:new THREE.MeshStandardMaterial({color:0x243239,roughness:.28,metalness:.2}),path:mat(0xaaa697),path2:mat(0x9f9e95),pathLine:mat(0x797c77),lantern:mat(0x4a3025),lanternGlow:new THREE.MeshStandardMaterial({color:0xffa94e,emissive:0xff6c1a,emissiveIntensity:1.8}),treeTrunk:mat(0x49372a),leaf:mat(0x3d6848),leaf2:mat(0x587b4b),metal:mat(0x818783,.35,.65),rope:mat(0xb7b5a9,.45,.35),ninjaCloth:mat(0x191c22),ninjaDark:mat(0x090c11),ninjaLeather:mat(0x5a4432),ninjaSkin:mat(0x9d7c64),red:mat(0x9c3931)});
 Object.assign(mats,{ninjaArmor:mat(0x252b34,.48,.28),ninjaAccent:mat(0x87352f,.72,.06),ninjaStitch:mat(0x9b8b70,.9,0),ninjaSole:mat(0x17191e,.95,0),roofDeck:mat(0x77766f,.96,0),roofEdge:mat(0xaaa493,.9,0),roofMark:mat(0xb9a77f,.85,0),roofMetal:mat(0x56636a,.42,.48),roofGlass:new THREE.MeshStandardMaterial({color:0x647c82,roughness:.22,metalness:.25,transparent:true,opacity:.72})});makeDetailMats();
 worldRoot=new THREE.Group();scene.add(worldRoot);
 const ground=new THREE.Mesh(new THREE.CircleGeometry(WORLD.groundRadius,128),mats.grass);ground.rotation.x=-Math.PI/2;ground.position.y=-.12;ground.receiveShadow=true;worldRoot.add(ground);
 // Dirt and stone streets beneath the districts.
 paveBox(280,25,mats.cobble,-1,.01,0,5,.06);paveBox(25,240,mats.cobble,0,.02,0,5,.065);buildStreetDetails();
 for(let i=0;i<6;i++){const cx=[-88,0,88][i%3],cz=i<3?-60:60;buildDistrict(i,cx,cz);ui.loadbar.style.width=`${8+(i+1)*12}%`;ui.loadtext.textContent=`Constructing district ${i+1} / 6`;}
 buildOuterWall();
 // Landmark plaza, well and bridges connecting the district grid.
 const plaza=new THREE.Mesh(new THREE.CylinderGeometry(12,12,.05,48),mats.path2);plaza.position.set(0,.025,0);plaza.receiveShadow=true;worldRoot.add(plaza);
 for(let i=-4;i<=4;i++){if(i===0)continue;makeLantern(i*22,-3);if(i%2===0)makeLantern(i*22,3);}
 createRepeatedInstances();buildDetailInstances();batchStaticBoxMeshes();
 ui.loadbar.style.width='100%';ui.loadtext.textContent='Village ready';worldBuilt=true;
}
function buildGrappleTargets(){
 // Every tangible world mesh is a valid grapple surface (ground, structures, props and roofs).
 // There is deliberately no sky mesh in the world, so aiming into the sky cannot attach.
 grappleTargetMeshes.length=0;worldRoot.updateMatrixWorld(true);
 worldRoot.traverse(obj=>{
  if(!obj.isMesh||!obj.visible)return;
  if(obj.name==='LanternFakeLightPatches'||obj.name==='PooledSlideDust'||obj.name==='GrassTufts'||obj.name==='Flowers'||obj.name==='FlowerStems'||obj.name==='Pebbles'||obj.name==='Bushes'||obj.name==='TreeLeaves'||obj.name==='PotPlant'||obj.name==='PetalDecal')return;
  grappleTargetMeshes.push(obj);
 });
}
function buildPlayer(){
 playerMesh=new THREE.Group();playerMesh.name='FirstPersonNinjaRig';scene.add(playerMesh);
 // A coordinated procedural rig: all body parts are attached to the torso/limb pivots.
 const part=(geometry,material,parent,x=0,y=0,z=0,scale=null)=>{const m=new THREE.Mesh(geometry,material);m.position.set(x,y,z);if(scale)m.scale.set(scale[0],scale[1],scale[2]);m.castShadow=false;m.receiveShadow=false;parent.add(m);return m;};
 const box=(w,h,d,material,parent,x,y,z,rotZ=0)=>{const m=part(new THREE.BoxGeometry(w,h,d),material,parent,x,y,z);m.rotation.z=rotZ;return m;};
 torso=new THREE.Group();torso.name='TorsoRig';torso.position.set(0,1.16,0);playerMesh.add(torso);
 // Layered cloth and light tactical chest armor.
 part(new THREE.CapsuleGeometry(.245,.37,4,9),mats.ninjaCloth,torso,0,-.015,0,[1.18,1.12,.78]);
 part(new THREE.BoxGeometry(.48,.27,.055),mats.ninjaArmor,torso,0,.065,-.153);
 part(new THREE.BoxGeometry(.42,.055,.025),mats.ninjaDark,torso,0,.15,-.19);
 part(new THREE.BoxGeometry(.24,.11,.035),mats.ninjaAccent,torso,0,.03,-.193);
 // Cross-body harness, stitching and shoulder guards.
 const strapL=box(.055,.58,.028,mats.ninjaLeather,torso,-.12,.035,-.188,-.39);
 const strapR=box(.055,.58,.028,mats.ninjaLeather,torso,.12,.035,-.188,.39);
 box(.065,.60,.03,mats.ninjaStitch,torso,-.12,.035,-.208,-.39);
 box(.065,.60,.03,mats.ninjaStitch,torso,.12,.035,-.208,.39);
 box(.55,.095,.37,mats.ninjaLeather,torso,0,-.24,0);
 box(.59,.09,.39,mats.ninjaDark,torso,0,-.315,0);
 box(.12,.13,.035,mats.ninjaArmor,torso,0,-.275,-.205);
 box(.055,.065,.025,mats.ninjaStitch,torso,0,-.275,-.228);
 // A layered collar sits below the camera line, with a scarf edge and subtle red seam.
 const collar=part(new THREE.TorusGeometry(.235,.064,8,22),mats.ninjaDark,torso,0,.25,0);collar.rotation.x=Math.PI/2;
 const scarf=part(new THREE.TorusGeometry(.239,.025,6,22),mats.ninjaAccent,torso,0,.215,0);scarf.rotation.x=Math.PI/2;
 // Utility pouches and blade/sheath details on the waist.
 for(const side of [-1,1]){
  box(.14,.17,.13,mats.ninjaLeather,torso,side*.29,-.23,-.06,side*-.05);
  box(.10,.035,.14,mats.ninjaStitch,torso,side*.29,-.17,-.07,side*-.05);
 }
 // Loose cloth tails give the lower torso a readable silhouette while looking down.
 waistTails=[];
 for(const side of [-1,1]){const tail=new THREE.Group();tail.position.set(side*.19,-.30,-.10);torso.add(tail);part(new THREE.BoxGeometry(.13,.34,.045),mats.ninjaAccent,tail,side*-.025,-.16,-.08, [1,.98,1]);part(new THREE.BoxGeometry(.09,.28,.025),mats.ninjaCloth,tail,side*-.025,-.15,-.108);waistTails.push({side,group:tail});}
 arms=[];legs=[];hands=[];grappleDevices=[];
 for(const side of [-1,1]){
  // Articulated arms with shoulder cap, stitched sleeve, bracer, wrist cuff and gloved fingers.
  const shoulder=part(new THREE.SphereGeometry(.145,10,8),mats.ninjaArmor,torso,side*.315,.28,-.19,[1.05,.78,1.05]);
  const upper=new THREE.Group();upper.name=side<0?'LeftUpperArm':'RightUpperArm';upper.position.set(side*.335,.28,-.24);torso.add(upper);
  part(new THREE.CapsuleGeometry(.092,.285,4,8),mats.ninjaCloth,upper,0,-.145,-.01);
  part(new THREE.CapsuleGeometry(.026,.20,3,6),mats.ninjaAccent,upper,side*-.035,-.15,-.083,[1,.85,.65]);
  const upperBand=part(new THREE.CylinderGeometry(.101,.099,.045,9),mats.ninjaLeather,upper,0,-.27,-.01);upperBand.rotation.z=.04;
  const elbow=new THREE.Group();elbow.name=side<0?'LeftElbow':'RightElbow';elbow.position.set(0,-.295,-.035);upper.add(elbow);
  part(new THREE.SphereGeometry(.088,9,7),mats.ninjaArmor,elbow,0,0,-.005,[1,.95,1]);
  part(new THREE.CapsuleGeometry(.077,.245,4,8),mats.ninjaLeather,elbow,0,-.135,-.055);
  part(new THREE.CapsuleGeometry(.052,.185,4,7),mats.ninjaArmor,elbow,0,-.145,-.115,[1,.9,.75]);
  const wrist=part(new THREE.CylinderGeometry(.078,.075,.055,9),mats.ninjaAccent,elbow,0,-.255,-.075);wrist.rotation.z=.02;
  const hand=new THREE.Group();hand.name=side<0?'LeftGlovedHand':'RightGlovedHand';hand.position.set(0,-.292,-.135);elbow.add(hand);hand.userData.side=side;
  part(new THREE.BoxGeometry(.125,.095,.125),mats.ninjaDark,hand,0,0,-.018);
  part(new THREE.BoxGeometry(.135,.035,.07),mats.ninjaLeather,hand,0,.033,-.025);
  for(let finger=-1;finger<=1;finger++)part(new THREE.CapsuleGeometry(.018,.055,3,5),mats.ninjaDark,hand,finger*.036,-.038,-.083);
  part(new THREE.CapsuleGeometry(.02,.055,3,5),mats.ninjaDark,hand,side*-.071,-.005,-.047,[1,1,.9]);
  arms.push({side,shoulder,upper,elbow,hand});hands.push(hand);
  // Wrist-mounted twin-cable launcher with layered metal housing.
  const device=new THREE.Group();device.position.set(0,-.075,-.09);elbow.add(device);
  part(new THREE.BoxGeometry(.16,.085,.19),mats.metal,device,0,0,-.02);
  part(new THREE.BoxGeometry(.105,.04,.12),mats.ninjaArmor,device,0,.052,-.015);
  const barrel=part(new THREE.CylinderGeometry(.026,.032,.22,8),mats.metal,device,0,-.005,-.17);barrel.rotation.x=Math.PI/2;
  const muzzle=part(new THREE.TorusGeometry(.033,.008,5,9),mats.ninjaStitch,device,0,-.005,-.285);muzzle.rotation.x=Math.PI/2;
  grappleDevices.push({side,group:device,device,barrel});
  // Pants, knee pads, segmented shin guards and boots are attached to the hip pivot.
  const leg=new THREE.Group();leg.name=side<0?'LeftLeg':'RightLeg';leg.position.set(side*.18,.88,0);playerMesh.add(leg);
  part(new THREE.CapsuleGeometry(.112,.31,4,8),mats.ninjaCloth,leg,0,-.175,.005,[1.08,1,1]);
  part(new THREE.BoxGeometry(.105,.12,.045),mats.ninjaLeather,leg,side*-.025,-.19,-.09,side*-.08);
  const knee=new THREE.Group();knee.position.set(0,-.36,-.006);leg.add(knee);
  part(new THREE.SphereGeometry(.092,9,7),mats.ninjaLeather,knee,0,0,0,[1,.9,.85]);
  part(new THREE.BoxGeometry(.17,.135,.075),mats.ninjaArmor,knee,0,-.005,-.075,side*.04);
  part(new THREE.BoxGeometry(.12,.025,.025),mats.ninjaAccent,knee,0,.025,-.12);
  part(new THREE.CapsuleGeometry(.077,.27,4,8),mats.ninjaLeather,knee,0,-.16,-.025);
  part(new THREE.BoxGeometry(.118,.23,.043),mats.ninjaArmor,knee,0,-.16,-.086);
  for(const yy of [-.09,-.22])part(new THREE.BoxGeometry(.145,.027,.035),mats.ninjaStitch,knee,0,yy,-.105);
  const boot=new THREE.Group();boot.position.set(0,-.338,-.05);knee.add(boot);
  part(new THREE.BoxGeometry(.19,.115,.27),mats.ninjaDark,boot,0,-.035,-.055);
  part(new THREE.BoxGeometry(.195,.035,.285),mats.ninjaSole,boot,0,-.095,-.052);
  part(new THREE.BoxGeometry(.17,.06,.10),mats.ninjaLeather,boot,0,-.007,-.135);
  for(let i=-1;i<=1;i++)part(new THREE.BoxGeometry(.035,.012,.04),mats.ninjaStitch,boot,i*.045,.025,-.08);
  legs.push({side,leg,knee,boot,hipY:.88});
 }
}
function erikaNormName(name){return String(name||'').toLowerCase().replace(/[^a-z0-9]/g,'');}
function maskErikaHeadForFirstPerson(mesh, M){
 if(!mesh||!mesh.isSkinnedMesh||!mesh.skeleton||!mesh.geometry)return;
 const geometry=mesh.geometry, skinIndex=geometry.getAttribute('skinIndex'), skinWeight=geometry.getAttribute('skinWeight');
 if(!skinIndex||!skinWeight)return;
 const headBones=new Set();
 mesh.skeleton.bones.forEach((bone,i)=>{const n=erikaNormName(bone.name);if(n.endsWith('head')||n.includes('headtop')||n.includes('lefteye')||n.includes('righteye')||n.endsWith('jaw')||n.endsWith('teeth')||n.endsWith('ear'))headBones.add(i);});
 if(!headBones.size)return;
 const pos=geometry.getAttribute('position');if(!pos)return;
 const headWeight=new Float32Array(pos.count);
 for(let i=0;i<pos.count;i++){let sum=0;for(let j=0;j<4;j++){if(headBones.has(skinIndex.getComponent(i,j)))sum+=skinWeight.getComponent(i,j);}headWeight[i]=sum;}
 const sourceIndex=geometry.getIndex();const indexCount=sourceIndex?sourceIndex.count:pos.count;
 if(indexCount<3)return;
 const groups=geometry.groups.length?geometry.groups:[{start:0,count:indexCount,materialIndex:0}];
 const filtered=[],newGroups=[];let removed=0;
 for(const group of groups){const start=filtered.length;const end=Math.min(indexCount,group.start+group.count);
  for(let i=group.start;i+2<end;i+=3){const a=sourceIndex?sourceIndex.getX(i):i,b=sourceIndex?sourceIndex.getX(i+1):i+1,c=sourceIndex?sourceIndex.getX(i+2):i+2;const wa=headWeight[a]||0,wb=headWeight[b]||0,wc=headWeight[c]||0;const avg=(wa+wb+wc)/3;const clearlyHead=(wa>.35&&wb>.35&&wc>.35)||avg>.68;if(clearlyHead){removed++;continue;}filtered.push(a,b,c);}
  newGroups.push({start,count:filtered.length-start,materialIndex:group.materialIndex||0});
 }
 if(!removed||!filtered.length)return;
 const clone=geometry.clone();clone.setIndex(filtered);clone.clearGroups();for(const g of newGroups)if(g.count>0)clone.addGroup(g.start,g.count,g.materialIndex);mesh.geometry=clone;
}
function createErikaHookDevice(bone,side){
 if(!bone)return;
 const root=new THREE.Group();root.name=side<0?'LeftGrappleLauncher':'RightGrappleLauncher';
 const shell=new THREE.Mesh(new THREE.BoxGeometry(.105,.075,.19),mats.metal);shell.material=mats.metal;shell.castShadow=false;shell.receiveShadow=false;root.add(shell);shell.position.set(0,0,-.045);
 const top=new THREE.Mesh(new THREE.BoxGeometry(.075,.025,.11),mats.ninjaAccent);top.castShadow=false;top.receiveShadow=false;top.position.set(0,.046,-.035);root.add(top);
 const barrel=new THREE.Mesh(new THREE.CylinderGeometry(.021,.027,.17,8),mats.metal);barrel.rotation.x=Math.PI/2;barrel.position.set(0,0,-.17);barrel.castShadow=false;barrel.receiveShadow=false;root.add(barrel);
 root.position.set(0,0,0);bone.add(root);
}
// ===================================================================================
// Erika animation system — real FBX clips (Idle / Normal_Run / Fast_Run / Jumping / Slide / Hard_Landing)
// driven by the movement physics through a THREE.AnimationMixer.
//  * every clip is always "playing" at timeScale 0; this code sets each clip's time itself and cross-fades the
//    weights, so locomotion speed, jump height and slide length always match the physics exactly;
//  * loop clips keep the duplicated end-frame out of the cycle (no hitch at the loop point);
//  * root motion was removed from the clips when they were baked (the physics moves the player).
// ===================================================================================
const erikaAnim={ready:false,mixer:null,acts:{},durs:{},cur:{},vel:{},attackActs:{},rootMotion:{},attackName:'',attackUpper:{},atkFull:null,atkUpper:null,attackMove:0,runDir:1,lunged:false,attackAction:null,attackRootPosition:null,attackWeight:0,attackTarget:0,comboStep:-1,comboUntil:0,slideGap:1,phase:0,idleT:0,sp:0,jt:.8,slideT:0,climbT:0,wasSlide:false,landMode:0,landT:0,hardT:.57,lastLandEvent:0,heading:0,armW:0,tilt:0,mode:'ground',walkAimTime:0,tmp:null};
const ERIKA_CLIPS=['Idle','Normal_Run','Fast_Run','Jumping','Slide','Hard_Landing','Climb_Wall','Wall_Run_R','Wall_Run_L'];
const ERIKA_RUNTIME_CLIPS=[...ERIKA_CLIPS,'Walk_Aim'];
const ERIKA_CLIMB_MPS=.632;               // metres climbed per second of Climb_Wall playback at 1x
const ERIKA_FAST_PHASE=.969;               // phase offset that keeps both run cycles on the same foot while blending
// Cross-fade smoothing times (seconds). Weights follow a critically-damped spring, so a fade starts at zero
// velocity (no pop on the first frame) and settles without overshoot.
const ERIKA_FADE_IN={Idle:.16,Normal_Run:.17,Fast_Run:.17,Jumping:.13,Slide:.11,Hard_Landing:.07,Climb_Wall:.12,Wall_Run_R:.12,Wall_Run_L:.12,Walk_Aim:.10};
const ERIKA_FADE_OUT={Idle:.16,Normal_Run:.17,Fast_Run:.17,Jumping:.15,Slide:.17,Hard_Landing:.2,Climb_Wall:.14,Wall_Run_R:.14,Wall_Run_L:.14,Walk_Aim:.16};
function erikaSmoothDamp(cur,target,vel,smoothTime,dt){
 const o=2/smoothTime,x=o*dt,e=1/(1+x+.48*x*x+.235*x*x*x),ch=cur-target,tmp=(vel.v+o*ch)*dt;
 vel.v=(vel.v-o*tmp)*e;return target+(ch+tmp)*e;
}
function erikaSmoothstep(a,b,x){const t=Math.min(1,Math.max(0,(x-a)/(b-a)));return t*t*(3-2*t);}
function erikaClamp(x,a,b){return x<a?a:x>b?b:x;}
function erikaWrapPi(a){return a-Math.PI*2*Math.floor((a+Math.PI)/(Math.PI*2));}
function erikaInflateB64(s){   // "~<rawLength>:<base64 of raw-deflate data>" -> ArrayBuffer (lossless; see tools)
 const c=s.indexOf(':'),n=+s.slice(1,c),bin=atob(s.slice(c+1)),L=bin.length,src=new Uint8Array(L);for(let i=0;i<L;i++)src[i]=bin.charCodeAt(i);
 const out=new Uint8Array(n);let op=0,ip=0,bb=0,bc=0;
 const LB=[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258],LE=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0],
 DB=[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577],DE=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
 const bits=k=>{let v=bb;while(bc<k){v|=src[ip++]<<bc;bc+=8;}bb=v>>>k;bc-=k;return v&((1<<k)-1);};
 const build=(len,n0,n)=>{const cnt=new Uint16Array(16),sym=new Uint16Array(n),offs=new Uint16Array(16);for(let i=0;i<n;i++)cnt[len[n0+i]]++;cnt[0]=0;for(let i=1;i<15;i++)offs[i+1]=offs[i]+cnt[i];for(let i=0;i<n;i++)if(len[n0+i])sym[offs[len[n0+i]]++]=i;return{c:cnt,s:sym};};
 const dec=h=>{let code=0,first=0,index=0;for(let l=1;l<=15;l++){code|=bits(1);const k=h.c[l];if(code-k<first)return h.s[index+(code-first)];index+=k;first+=k;first<<=1;code<<=1;}throw new Error('bad inflate data');};
 let fl,fd;{const l=new Uint8Array(288);for(let i=0;i<288;i++)l[i]=i<144?8:i<256?9:i<280?7:8;fl=build(l,0,288);const d=new Uint8Array(30).fill(5);fd=build(d,0,30);}
 const codes=(hl,hd)=>{for(;;){let s=dec(hl);if(s<256)out[op++]=s;else if(s===256)return;else{s-=257;const len=LB[s]+bits(LE[s]),ds=dec(hd),dist=DB[ds]+bits(DE[ds]);for(let i=0;i<len;i++,op++)out[op]=out[op-dist];}}};
 let last;do{last=bits(1);const t=bits(2);
  if(t===0){bb=0;bc=0;const len=src[ip]|(src[ip+1]<<8);ip+=4;out.set(src.subarray(ip,ip+len),op);op+=len;ip+=len;}
  else if(t===1)codes(fl,fd);
  else{const nl=bits(5)+257,nd=bits(5)+1,nc=bits(4)+4,ord=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15],lens=new Uint8Array(320);
   for(let i=0;i<nc;i++)lens[ord[i]]=bits(3);const hc=build(lens,0,19);let i=0;const all=new Uint8Array(nl+nd);
   while(i<nl+nd){const s=dec(hc);if(s<16)all[i++]=s;else{let rep,v=0;if(s===16){v=all[i-1];rep=3+bits(2);}else if(s===17)rep=3+bits(3);else rep=11+bits(7);while(rep--)all[i++]=v;}}
   codes(build(all,0,nl),build(all,nl,nd));}
 }while(!last);
 return out.buffer;
}
function erikaB64(s){if(s.charCodeAt(0)===126)return erikaInflateB64(s);const bin=atob(s),n=bin.length,u=new Uint8Array(n);for(let i=0;i<n;i++)u[i]=bin.charCodeAt(i);return u.buffer;}
function buildErikaClips(M,data){
 const clips={};
 for(const name of ERIKA_CLIPS){
  const c=data[name];if(!c)throw new Error('Missing animation '+name);
  const times=new Float32Array(erikaB64(c.t)),tracks=[];
  for(const tr of c.tracks){
   const raw=erikaB64(tr.d);
   if(tr.k==='q'){
    const i16=new Int16Array(raw),vals=new Float32Array(i16.length);
    for(let i=0;i<i16.length;i+=4){const x=i16[i]/32767,y=i16[i+1]/32767,z=i16[i+2]/32767,w=i16[i+3]/32767,l=Math.hypot(x,y,z,w)||1;vals[i]=x/l;vals[i+1]=y/l;vals[i+2]=z/l;vals[i+3]=w/l;}
    tracks.push(new M.QuaternionKeyframeTrack(tr.b+'.quaternion',tr.c?[0]:times,vals));
   }else tracks.push(new M.VectorKeyframeTrack(tr.b+'.position',times,new Float32Array(raw)));
  }
  clips[name]=new M.AnimationClip(name,c.dur,tracks);
 }
 return clips;
}
function setupErikaAnimations(M,model,loader){
 const A=erikaAnim,node=document.getElementById('erikaAnimData');
 if(!node){console.warn('Erika animation data missing — using procedural pose.');return;}
 try{
  const clips=buildErikaClips(M,JSON.parse(node.textContent));
  const walkNode=document.getElementById('walkAimFbxData');
  if(walkNode){try{const walkModel=loader.parse(erikaB64(walkNode.textContent.trim()),''),walkClip=walkModel.animations&&walkModel.animations[0];if(!walkClip)throw new Error('FBX contains no animation clip');walkClip.tracks=walkClip.tracks.filter(track=>{const path=track.name.toLowerCase(),target=path.slice(0,path.lastIndexOf('.')).replace(/[^a-z0-9]/g,'');return !(path.endsWith('.position')&&(target.endsWith('hips')||target.endsWith('root')||target.endsWith('armature')));});walkClip.name='Walk_Aim';clips.Walk_Aim=walkClip;walkNode.remove();}catch(err){console.warn('Aim-walk animation could not be loaded:',err);}}
  if(!clips.Walk_Aim)clips.Walk_Aim=clips.Normal_Run;
  const dyingNode=document.getElementById('dyingBackwardsFbxData');
  if(dyingNode){try{
   const dm=loader.parse(erikaB64(dyingNode.textContent.trim()),''),dc=dm.animations&&dm.animations[0];if(!dc)throw new Error('FBX contains no animation clip');
   const idleHips=clips.Idle&&clips.Idle.tracks.find(t=>t.name==='mixamorigHips.position');
   const bx=idleHips?idleHips.values[0]:0,by=idleHips?idleHips.values[1]:96.8,bz=idleHips?idleHips.values[2]:1.6;
   const isHipsPos=t=>{const p=t.name.toLowerCase();return p.endsWith('.position')&&erikaNormName(p.slice(0,p.lastIndexOf('.'))).endsWith('hips');};
   const hp=dc.tracks.find(isHipsPos);
   dc.tracks=dc.tracks.filter(t=>t===hp||!t.name.toLowerCase().endsWith('.position'));   // only the hips translate
   if(hp&&hp.values.length>=3){const v=hp.values,x0=v[0],y0=v[1]||1,z0=v[2],k=by/y0;for(let i=0;i<v.length;i+=3){v[i]=bx+(v[i]-x0)*k;v[i+1]=Math.max(11,v[i+1]*k);v[i+2]=bz+(v[i+2]-z0)*k;}}   // clip was authored for a taller skeleton
   dc.name='Death';clips.Death=dc;dyingNode.remove();
  }catch(err){console.warn('Death animation could not be loaded:',err);}}
  const blockNode=document.getElementById('blockFbxData');
  if(blockNode){try{const bm=loader.parse(erikaB64(blockNode.textContent.trim()),''),bc=bm.animations&&bm.animations[0];if(!bc)throw new Error('FBX contains no animation clip');bc.tracks=bc.tracks.filter(track=>{const path=track.name.toLowerCase(),target=path.slice(0,path.lastIndexOf('.')).replace(/[^a-z0-9]/g,'');return !(path.endsWith('.position')&&(target.endsWith('hips')||target.endsWith('root')||target.endsWith('armature')));});bc.name='Block';clips.Block=bc;blockNode.remove();}catch(err){console.warn('Block animation could not be loaded:',err);}}
  const rollNode=document.getElementById('fallRollFbxData');
  if(rollNode){try{
   const rm=loader.parse(erikaB64(rollNode.textContent.trim()),''),rc=rm.animations&&rm.animations[0];if(!rc)throw new Error('FBX contains no animation clip');
   const idleHips=clips.Idle&&clips.Idle.tracks.find(t=>t.name==='mixamorigHips.position');
   const bx=idleHips?idleHips.values[0]:0,by=idleHips?idleHips.values[1]:96.8,bz=idleHips?idleHips.values[2]:1.6;
   const isHipsPos=t=>{const p=t.name.toLowerCase();return p.endsWith('.position')&&erikaNormName(p.slice(0,p.lastIndexOf('.'))).endsWith('hips');};
   const hp=rc.tracks.find(isHipsPos);
   rc.tracks=rc.tracks.filter(t=>t===hp||!t.name.toLowerCase().endsWith('.position'));   // only the hips translate
   if(hp&&hp.values.length>=3){const v=hp.values,n=hp.times.length,yEnd=v[(n-1)*3+1]||by,k=by/yEnd,x0=v[0],rz=new Float32Array(n);
    for(let i=0;i<n;i++){rz[i]=v[i*3+2]*k;v[i*3]=bx+(v[i*3]-x0)*k;v[i*3+1]=Math.max(8,v[i*3+1]*k);v[i*3+2]=bz;}   // forward travel is taken out of the hips and applied to the player instead
    A.rollRM={times:Float32Array.from(hp.times),z:rz};}
   rc.name='FallRoll';clips.FallRoll=rc;rollNode.remove();
  }catch(err){console.warn('Fall-roll animation could not be loaded:',err);}}
  A.mixer=new M.AnimationMixer(model);A.attackRootPosition=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.hips?erikaPlayer.bones.hips.position.clone():null;
  for(const n of ERIKA_RUNTIME_CLIPS){const act=A.mixer.clipAction(clips[n]);act.setLoop(M.LoopRepeat,Infinity);act.timeScale=0;act.enabled=true;act.setEffectiveWeight(n==='Idle'?1:0);act.play();A.acts[n]=act;A.durs[n]=clips[n].duration;A.cur[n]=n==='Idle'?1:0;A.vel[n]={v:0};}
  if(clips.Death){const da=A.mixer.clipAction(clips.Death);da.setLoop(M.LoopOnce,1);da.clampWhenFinished=true;da.timeScale=0;da.enabled=true;da.setEffectiveWeight(0);da.play();A.deathAct=da;A.durs.Death=clips.Death.duration;}
  if(clips.Block){const ba=A.mixer.clipAction(clips.Block);ba.setLoop(M.LoopRepeat,Infinity);ba.timeScale=0;ba.enabled=true;ba.setEffectiveWeight(0);ba.play();A.blockAct=ba;A.durs.Block=clips.Block.duration;}
  if(clips.FallRoll&&A.rollRM){const ra=A.mixer.clipAction(clips.FallRoll);ra.setLoop(M.LoopOnce,1);ra.clampWhenFinished=true;ra.timeScale=0;ra.enabled=true;ra.setEffectiveWeight(0);ra.play();A.rollAct=ra;A.durs.FallRoll=clips.FallRoll.duration;}
  A.attackActs={};
  const attackAssets=[['SwordSlash','swordSlashFbxData'],['SecondSwordSlash','secondSwordSlashFbxData'],['ThirdSwordSlash','thirdSwordSlashFbxData']];
  for(const [name,id] of attackAssets){
   const attackNode=document.getElementById(id);if(!attackNode){console.warn('Missing sword animation data:',id);continue;}
   try{
    const attackModel=loader.parse(erikaB64(attackNode.textContent.trim()),'');
    const clip=attackModel.animations&&attackModel.animations[0];if(!clip)throw new Error('FBX contains no animation clip');
    {const hp=clip.tracks.find(tr=>{const p=tr.name.toLowerCase();return p.endsWith('.position')&&p.slice(0,p.lastIndexOf('.')).replace(/[^a-z0-9]/g,'').endsWith('hips');});
     if(hp&&hp.times.length>1){const n=hp.times.length,v=hp.values,rm={times:Float32Array.from(hp.times),x:new Float32Array(n),z:new Float32Array(n),y0:v[1]};for(let i=0;i<n;i++){rm.x[i]=v[i*3]-v[0];rm.z[i]=v[i*3+2]-v[2];}rm.dist=Math.hypot(rm.x[n-1],rm.z[n-1]);A.rootMotion[name]=rm;}}
    clip.tracks=clip.tracks.filter(track=>{const path=track.name.toLowerCase(),target=path.slice(0,path.lastIndexOf('.')).replace(/[^a-z0-9]/g,'');return !(path.endsWith('.position')&&(target.endsWith('hips')||target.endsWith('root')||target.endsWith('armature')));});
    clip.name=name;const action=A.mixer.clipAction(clip);action.setLoop(M.LoopOnce,1);action.clampWhenFinished=true;action.setEffectiveWeight(0);A.attackActs[name]=action;
    const upperClip=clip.clone();upperClip.name=name+'_Upper';
    upperClip.tracks=upperClip.tracks.filter(tr=>{const n=erikaNormName(tr.name.slice(0,tr.name.lastIndexOf('.')));return /spine|neck|head|shoulder|arm|hand|thumb|index|middle|ring|pinky/.test(n)&&!/armature|leg|foot|toe|hips/.test(n);});
    if(upperClip.tracks.length){const upperAction=A.mixer.clipAction(upperClip);upperAction.setLoop(M.LoopOnce,1);upperAction.clampWhenFinished=true;upperAction.setEffectiveWeight(0);A.attackUpper[name]=upperAction;A.hasUpper=true;}else console.warn('Upper-body slash layer has no matching bones:',name);
    attackNode.remove();
   }catch(err){console.warn('Sword animation could not be loaded:',name,err);}
  }
  A.tmp={q:new M.Quaternion(),t:new M.Quaternion(),e:new M.Euler()};
  A.ready=true;try{setupErikaAim(M,model);}catch(err){console.warn('Bow aim animation setup failed.',err);}node.remove();
 }catch(err){console.warn('Erika animation setup failed — using procedural pose.',err);A.ready=false;}
}
function resetErikaAnimation(){
 const A=erikaAnim;if(!A.ready)return;
 for(const n of ERIKA_RUNTIME_CLIPS){A.cur[n]=n==='Idle'?1:0;A.vel[n].v=0;}A.walkAimTime=0;
 if(A.deathAct){A.deathAct.setEffectiveWeight(0);A.deathAct.time=0;}if(A.rollAct)A.rollAct.setEffectiveWeight(0);player.fallRoll=null;
 if(A.attackAction)A.attackAction.stop();for(const action of Object.values(A.attackActs))action.stop();for(const action of Object.values(A.attackUpper))action.stop();
 A.atkFull=null;A.atkUpper=null;A.attackMove=0;A.runDir=1;A.attackAction=null;A.attackWeight=0;A.attackTarget=0;A.comboStep=-1;A.comboUntil=0;
 A.slideGap=1;A.phase=0;A.idleT=0;A.sp=0;A.jt=.8;A.slideT=0;A.climbT=0;A.wasSlide=false;A.landMode=0;A.landT=0;A.lastLandEvent=player.landEvent;A.heading=0;A.tilt=0;A.mode='ground';
}

// ===================== FALL ROLL: a big drop (off a tall building) with no sword strike -> "Falling To Roll" =====================
// Tweak live: FALLROLL.minImpact (landing speed in m/s; gravity is 24, so 20 ~ an 8 m drop), FALLROLL.enabled=false, FALLROLL.start/.end (clip seconds played)
const FALLROLL={enabled:true,minImpact:20,start:.4,end:1.8,speed:2,fadeIn:.05,free:.6,ev:0};   // free: fraction of the roll after which the player regains control (walk / attack) while the clip fades out
function rollLocked(){const R=player.fallRoll;return !!R&&!R.free;}
function fallRollTick(dt){const R=player.fallRoll;if(!R||!R.free)return;R.t+=dt;if(R.t>=R.dur)player.fallRoll=null;}
function fallRollCheck(){
 const P=player,A=erikaAnim;
 if(P.landEvent===FALLROLL.ev)return;FALLROLL.ev=P.landEvent;
 if(!FALLROLL.enabled||P.fallRoll||!A.ready||!A.rollAct||playerDeath.active||!P.grounded)return;
 if(P.landImpact<FALLROLL.minImpact)return;
 if(P.slam||P.lunge||P.kick||P.dash||P.block||P.mantle||P.climbing||A.attackAction)return;   // only a plain fall: never after / during a sword strike or slam
 const hv=Math.hypot(P.vel.x,P.vel.z);
 P.fallRoll={t:0,dur:(FALLROLL.end-FALLROLL.start)/FALLROLL.speed,dir:hv>2?Math.atan2(-P.vel.x,-P.vel.z):P.yaw,started:false,free:false,freeT:0};P.fallRoll.freeT=P.fallRoll.dur*FALLROLL.free;
 A.lastLandEvent=P.landEvent;A.landMode=0;A.slashQ=0;
 try{lungeHoldCancel();stopAim();cancelBowDraw();}catch(e){}
 P.sliding=false;P.jumpBuffer=0;P.vel.x=0;P.vel.z=0;
 try{slamFx.shake=Math.max(slamFx.shake||0,.3);if(HFX.ready)hfxPut(HFX.rings,_lg.fv.set(P.pos.x,P.pos.y+.1,P.pos.z),.35,.7,8,0xcfc2a8);}catch(e){}
}
function rollZAt(rm,t){const ts=rm.times,n=ts.length;if(t<=ts[0])return rm.z[0];if(t>=ts[n-1])return rm.z[n-1];let i=0;while(i<n-2&&t>ts[i+1])i++;return rm.z[i]+(rm.z[i+1]-rm.z[i])*(t-ts[i])/(ts[i+1]-ts[i]);}
function fallRollSafe(dt,oldPos){   // replaces the normal movement while rolling: the clip's forward travel moves the player (collisions still apply)
 const R=player.fallRoll,A=erikaAnim;if(!R)return;
 player.vel.x=0;player.vel.z=0;player.sliding=false;player.jumpBuffer=0;
 const t0=FALLROLL.start+R.t*FALLROLL.speed;R.t+=dt;if(R.t>=R.freeT)R.free=true;const t1=Math.min(FALLROLL.end,FALLROLL.start+R.t*FALLROLL.speed);
 let dz=0;if(A.rollRM&&erikaPlayer&&erikaPlayer.root)dz=(rollZAt(A.rollRM,t1)-rollZAt(A.rollRM,t0))*erikaPlayer.root.getWorldScale(_rmV).x;
 attackRootDisp.set(-Math.sin(R.dir)*dz,0,-Math.cos(R.dir)*dz);   // added to the position inside resolveMovement
 resolveMovement(oldPos,dt);
 if(R.t>=R.dur)player.fallRoll=null;
}
function erikaRollBlend(dt){   // control is back: normal locomotion plays and the roll clip fades out on top of it
 const A=erikaAnim,R=player.fallRoll,act=A.rollAct;
 const w=1-erikaSmoothstep(R.freeT,R.dur,R.t);
 act.time=Math.min(FALLROLL.start+R.t*FALLROLL.speed,A.durs.FallRoll-.001);act.setEffectiveWeight(w);
 return w;
}
function erikaRollPose(dt){
 const A=erikaAnim,R=player.fallRoll,P=player,act=A.rollAct;
 if(!R.started){R.started=true;act.reset();act.timeScale=0;act.enabled=true;act.play();}
 const w=erikaSmoothstep(0,FALLROLL.fadeIn,R.t);
 if(R.t>FALLROLL.fadeIn+.03){for(const n of ERIKA_RUNTIME_CLIPS){A.cur[n]=n==='Idle'?1:0;A.vel[n].v=0;}}   // while the roll hides the base pose, switch it to standing so the end of the roll fades into Idle
 for(const n of ERIKA_RUNTIME_CLIPS)A.acts[n].setEffectiveWeight(A.cur[n]*(1-w));
 act.time=Math.min(FALLROLL.start+R.t*FALLROLL.speed,A.durs.FallRoll-.001);act.setEffectiveWeight(w);
 const tgt=thirdPerson?erikaWrapPi(R.dir-P.yaw):0;A.heading+=erikaWrapPi(tgt-A.heading)*(1-Math.exp(-16*dt));
 A.tilt*=Math.exp(-10*dt);if(playerMesh)playerMesh.rotation.z=A.tilt;
 A.mixer.update(dt);A.armW=0;
}
function erikaBlockPose(dt){   // "Standing Block Idle": cross-fades in over the normal pose, holds while guarding, fades out
 const A=erikaAnim,B=player.block,act=A.blockAct,dur=A.durs.Block||1.8;
 if(!B.started){B.started=true;act.reset();act.timeScale=0;act.enabled=true;act.play();}
 const w=erikaSmoothstep(0,.07,B.t)*(1-erikaSmoothstep(BLOCK.dur-.1,BLOCK.dur,B.t));
 for(const n of ERIKA_RUNTIME_CLIPS)A.acts[n].setEffectiveWeight(A.cur[n]*(1-w));
 act.time=Math.min(B.t,dur-.001);act.setEffectiveWeight(w);
 A.mixer.update(dt);A.armW=0;
}
function erikaDeathPose(dt){   // "Dying Backwards": cross-fade from whatever pose the player was in, then play the clip once
 const A=erikaAnim,D=playerDeath,act=A.deathAct,dur=A.durs.Death;
 if(!D.started){
  D.started=true;
  if(A.attackAction)A.attackAction.stop();for(const a of Object.values(A.attackActs))a.stop();for(const a of Object.values(A.attackUpper))a.stop();
  A.attackAction=null;A.atkFull=null;A.atkUpper=null;A.atkPrev=null;A.atkPrevUp=null;A.attackWeight=0;A.attackTarget=0;A.attackMove=0;A.comboStep=-1;A.comboUntil=0;
  act.reset();act.timeScale=0;act.enabled=true;act.play();
 }
 const w=erikaSmoothstep(0,.2,D.t);
 for(const n of ERIKA_RUNTIME_CLIPS)A.acts[n].setEffectiveWeight(A.cur[n]*(1-w));
 act.time=Math.min(D.t,dur-.001);act.setEffectiveWeight(w);
 A.mixer.update(dt);
 A.armW=0;
}
// Arm pose that sits on top of the clips: first-person framing of the forearms and the forward "grapple" reach.
function erikaArmPose(bone,x,y,z,w){
 if(!bone)return;const base=erikaPlayer.rest.get(bone);if(!base)return;const T=erikaAnim.tmp;
 T.e.set(x,y,z,'XYZ');T.q.setFromEuler(T.e);T.t.copy(base).multiply(T.q);bone.quaternion.slerp(T.t,w);
}
function applyErikaArmOverride(w){
 const b=erikaPlayer.bones,state=player.state,speed=player.moveSpeed,moving=player.grounded&&!player.sliding&&speed>.65;
 const sprint=state==='SPRINTING',flight=state==='GRAPPLING'||state==='HOOK LAUNCH'||!!player.postFlight,sliding=player.sliding,wall=player.onWall||player.climbing,airborne=!player.grounded&&!flight;
 const pace=erikaClamp(speed/(sprint?14:8),0,1),wave=Math.sin(walkBob),waveR=Math.sin(walkBob+Math.PI);
 const lowerPose=thirdPerson?.94:sliding?.4:wall?.30:.62;
 const bw=bow.equip,bd=bow.draw;
 for(const side of [-1,1]){
  const phase=side<0?wave:waveR;
  const armSwing=moving?phase*(sprint?.34:.22)*pace:0;
  // Cables now leave from the hips, so in flight the arms hang free beside the launchers (ready for the bow).
  let armDown=flight?(thirdPerson?.62:.5):sliding?-.26:wall?.35:airborne?-.08:(thirdPerson?(moving?.88:lowerPose):lowerPose);
  let armForward=flight?.12:sliding?-.20:wall?.35:moving?(thirdPerson?.10:.36):(thirdPerson?.02:.28);
  let shoulderX=flight?-.05:sliding?.16:wall?.10:airborne?-.16:0;
  let elbowBend=flight?.5:sliding?.58:wall?.22:airborne?.48:moving?(sprint?.16:.10)+Math.max(0,-phase)*.27:.12;
  if(bw>.002){
   // Bow stance: left arm holds the bow out toward the target, right arm draws the string.
   const bowArm=side<0;let tDown=bowArm?(thirdPerson?-.07:.02):.10,tFwd=bowArm?(thirdPerson?.90:1.02):.55,tSh=bowArm?-.2:-.1,tEl=bowArm?.10:(.75+.55*bd);if(flight&&thirdPerson&&!bowArm){tDown=-.02;tFwd=1.05;tSh=-.08;tEl=1.0+.45*bd;}
   armDown+=(tDown-armDown)*bw;armForward+=(tFwd-armForward)*bw;shoulderX+=(tSh-shoulderX)*bw;elbowBend+=(tEl-elbowBend)*bw;
  }
  if(!thirdPerson&&(side>0?sword.hold:sword.lhold)>.002){const sh=side>0?sword.hold:sword.lhold;armDown+=(.02-armDown)*sh;armForward+=(1.0-armForward)*sh;shoulderX+=(-.2-shoulderX)*sh;elbowBend+=(.5-elbowBend)*sh;}
  const swing=armSwing*(1-bw)*(1-.6*(side>0?sword.hold:sword.lhold));
  const shoulderZ=(side<0?1:-1)*(armDown+swing*(side<0?1:-1));
  erikaArmPose(side<0?b.leftArm:b.rightArm,shoulderX,(side<0?-1:1)*armForward,shoulderZ,w);
  erikaArmPose(side<0?b.leftForeArm:b.rightForeArm,-elbowBend,0,(side<0?1:-1)*(flight?.05:.025),w);
  erikaArmPose(side<0?b.leftHand:b.rightHand,flight?-.10:0,(side<0?1:-1)*(flight?.05:.015),0,w);
 }
}
// ---- Wall-run pose (third person). Tweak: WALLRUN_POSE.lean (radians of body lean toward the wall), WALLRUN_POSE.reach (arm length used to put the palm on the wall)
const WALLRUN_POSE={lean:.3,reach:.68,wallDist:.45};   // lean: body tilts AWAY from the wall; wallDist: how far the feet run from the wall (m)
function applyWallRunPose(w,side){   // side: +1 wall on the right, -1 wall on the left (blended while it flips)
 const b=erikaPlayer.bones,A=erikaAnim,P=WALLRUN_POSE,rho=P.lean*Math.abs(side),wave=Math.sin(A.phase*Math.PI*2);
 // distance from the wall-side shoulder to the wall plane, given the lean, then the arm angle (below horizontal) that lays the palm flat on it
 const r=P.wallDist+1.35*Math.sin(rho)-.2*Math.cos(rho);
 const onWallDown=erikaClamp(Math.acos(erikaClamp(r/P.reach,0,1))+rho,-.1,1.2);
 const airDown=-.42;   // other arm: out and slightly up, in the air, for balance
 for(const s of [-1,1]){   // s = -1 left arm, +1 right arm
  const wt=erikaClamp(.5+.5*side*s,0,1);   // 1 = this arm is on the wall side
  const down=airDown+(onWallDown-airDown)*wt,fwd=(.18+.12*wave*s)*wt+(.35+.28*wave*s)*(1-wt)-.05,elbow=.12*wt+.55*(1-wt),sh=-.04*wt+.12*(1-wt);
  erikaArmPose(s<0?b.leftArm:b.rightArm,sh,(s<0?-1:1)*fwd,(s<0?1:-1)*down,w);
  erikaArmPose(s<0?b.leftForeArm:b.rightForeArm,-elbow,0,(s<0?1:-1)*.02,w);
  erikaArmPose(s<0?b.leftHand:b.rightHand,wt*-.12,0,0,w*wt);   // wall-side palm pressed flat
 }
}
function animateErika(dt){
 if(!erikaPlayer||!erikaPlayer.bones)return;
 const A=erikaAnim;
 if(!A.ready){animateErikaLegacy(dt);return;}
 dt=erikaClamp(dt,0,.1);
 if(playerDeath.active&&A.deathAct){erikaDeathPose(dt);return;}
 if(player.fallRoll&&A.rollAct){if(!player.fallRoll.free){A.rollW=1;erikaRollPose(dt);return;}A.rollW=erikaRollBlend(dt);}else{A.rollW=0;if(A.rollAct&&A.rollAct.getEffectiveWeight()>0)A.rollAct.setEffectiveWeight(0);}
 if(A.blockAct){if(player.block){erikaBlockPose(dt);return;}else if(A.blockAct.getEffectiveWeight()>0)A.blockAct.setEffectiveWeight(0);}
 const P=player,hs=P.moveSpeed,state=P.state;
 const flight=state==='GRAPPLING'||!!player.postFlight,launching=state==='HOOK LAUNCH';
 A.sp+=(hs-A.sp)*(1-Math.exp(-10*dt));
 // ---- landing events recorded by the physics
 if(P.landEvent!==A.lastLandEvent){
  A.lastLandEvent=P.landEvent;
  if(P.landImpact>=13){A.landMode=2;A.hardT=.57;}
  else if(P.landImpact>8){A.landMode=1;A.landT=0;}
 }
 const airborne=!P.grounded&&(P.airTime>.09||P.vel.y>1.5);
 if(!P.grounded&&A.landMode)A.landMode=0;
 // ---- choose the animation mode (priority order)
 let mode;
 if(flight)mode='flight';else if(P.mantle)mode='mantle';else if(P.climbing)mode='climb';else if(P.onWall)mode='wall';else if(airborne)mode='air';else if(P.sliding)mode='slide';
 else if(A.landMode===2)mode='hard';else if(A.landMode===1)mode='land';else mode='ground';
 A.mode=mode;
 // ---- per-mode clocks
 if(mode==='slide'){
  if(!A.wasSlide&&!(A.slideGap<.15&&A.slideT>0))A.slideT=0;   // a re-triggered slide continues instead of restarting
  A.slideT=A.slideT<.42?Math.min(.42,A.slideT+dt*1.15):Math.min(.95,A.slideT+dt*.22);
  A.slideGap=0;
 }else{
  A.slideGap+=dt;
  if(A.slideT>0){A.slideT=Math.min(1.5,A.slideT+dt*1.4);if(A.cur.Slide<.01&&A.slideGap>.3)A.slideT=0;}
 }
 A.wasSlide=mode==='slide';
 if(mode==='hard'){
  A.hardT+=dt*1.3;
  const wantsMove=hs>3||keys.KeyW||keys.KeyA||keys.KeyS||keys.KeyD;
  if((A.hardT>=.95&&wantsMove)||A.hardT>=1.95)A.landMode=0;
 }
 if(mode==='land'){A.landT+=dt;if(A.landT>(A.sp>5?.14:.26))A.landMode=0;}
 // ---- weight targets
 const T={Idle:0,Normal_Run:0,Fast_Run:0,Jumping:0,Slide:0,Hard_Landing:0,Climb_Wall:0,Wall_Run_R:0,Wall_Run_L:0,Walk_Aim:0};
 let jt=A.jt;
 if(mode==='ground'){
  if(weapon==='bow'&&bow.aimW>.01&&P.moveSpeed>.65&&!P.sliding)T.Walk_Aim=1;
  else{const wIdle=1-erikaSmoothstep(.4,2.2,A.sp),wMove=1-wIdle,wFast=wMove*erikaSmoothstep(8.5,11.5,A.sp);
  T.Idle=wIdle;T.Fast_Run=wFast;T.Normal_Run=wMove-wFast;}
 }else if(mode==='climb')T.Climb_Wall=1;
 else if(mode==='mantle'){const mu=P.mantle?P.mantle.t/P.mantle.dur:1,k=erikaSmoothstep(.62,.97,mu);T.Climb_Wall=1-k;T.Idle=k;}
 else if(mode==='wall'){
  // which side of the runner the wall is on (relative to the direction of travel) picks the right / left wall-run clip
  let fx=P.vel.x,fz=P.vel.z;if(fx*fx+fz*fz<1){fx=-Math.sin(P.yaw);fz=-Math.cos(P.yaw);}
  const fl=Math.hypot(fx,fz)||1;fx/=fl;fz/=fl;
  const sideRel=(-fz)*(-P.wallNormal.x)+fx*(-P.wallNormal.z);   // >0: wall on the right-hand side
  A.wallR=erikaSmoothstep(-.25,.25,sideRel);
  T.Wall_Run_R=A.wallR;T.Wall_Run_L=1-A.wallR;
 }
 else if(mode==='air'||mode==='flight'||mode==='land'){
  T.Jumping=1;
  if(mode==='flight')jt=.78;
  else if(mode!=='land'){const vy=P.vel.y;jt=vy>0?.47+.33*erikaClamp((9.5-vy)/9.5,0,1):.8+.28*erikaClamp(-vy/9.5,0,1);}
 }else if(mode==='slide')T.Slide=1;
 else if(mode==='hard')T.Hard_Landing=1;
 // jump clip time follows the physics (smoothed); snap while the clip is invisible so it never scrubs into view
 if(A.cur.Jumping<.02)A.jt=jt;else if(mode==='land')A.jt=Math.min(1.45,A.jt+dt*1.4);else A.jt+=(jt-A.jt)*(1-Math.exp(-16*dt));
 // ---- cross-fade weights (exponential, always normalised)
 let sum=0;
 for(const n of ERIKA_RUNTIME_CLIPS){
  const t=T[n],c=A.cur[n];
  let v=erikaSmoothDamp(c,t,A.vel[n],t>c?ERIKA_FADE_IN[n]:ERIKA_FADE_OUT[n],dt);
  v=erikaClamp(v,0,1);if(t===0&&v<.004){v=0;A.vel[n].v=0;}A.cur[n]=v;sum+=v;
 }
 if(sum<1e-4){A.cur.Idle=1;sum=1;}
 // Sword layering: standing still -> the full-body slash; moving -> only the upper body slashes while the legs keep running.
 A.attackMove+=(((SWORD_ATK.layered&&mode==='ground'&&A.sp>1.3&&A.hasUpper)?1:0)-A.attackMove)*(1-Math.exp(-9*dt));
 const atkW=A.attackWeight,atkMv=A.attackMove,locoScale=(1-atkW*(1-atkMv))*(1-(A.rollW||0));
 for(const n of ERIKA_RUNTIME_CLIPS){A.cur[n]/=sum;A.acts[n].setEffectiveWeight(A.cur[n]*locoScale);}
 swordPump(A,dt);
 if(A.attackAction&&!A.attackAction.isRunning()){
  const completedStep=A.comboStep;A.attackAction=null;A.attackTarget=0;
  A.comboUntil=performance.now()+SWORD_COMBO_WINDOW;   // loop: after the 3rd slash the next one is slash 1 again, with no dead time
 }
 A.attackWeight+=(A.attackTarget-A.attackWeight)*(1-Math.exp(-(A.attackTarget>0?18:9)*dt));
 if(A.atkFull){
  const fw=A.attackWeight*(1-A.attackMove),uw=A.attackWeight*A.attackMove/(1-Math.min(A.attackWeight,.97));
  const xf=A.atkPrev?Math.min(1,A.xfade||0):1;A.atkFull.setEffectiveWeight(fw*xf);if(A.atkUpper)A.atkUpper.setEffectiveWeight(uw*xf);if(A.atkPrev){A.atkPrev.setEffectiveWeight(fw*(1-xf));if(A.atkPrevUp)A.atkPrevUp.setEffectiveWeight(uw*(1-xf));}
  if(!A.attackAction&&A.attackWeight<.02){A.atkFull.stop();if(A.atkUpper)A.atkUpper.stop();A.atkFull=null;A.atkUpper=null;A.attackWeight=0;}
 }
 // ---- clip clocks
 const wallLoco=A.cur.Wall_Run_R+A.cur.Wall_Run_L,runLoco=A.cur.Normal_Run+A.cur.Fast_Run+wallLoco;
 if(mode==='ground'&&runLoco<.01&&T.Idle>.95)A.phase=0;      // always start a run on the same foot
 const rateRun=erikaClamp(A.sp/5.6,.55,1.25)/A.durs.Normal_Run;
 const rateFast=erikaClamp(A.sp/11,.9,1.3)/A.durs.Fast_Run;
 const mix=(A.cur.Fast_Run+wallLoco)/(runLoco+1e-4);
 {const fxw=-Math.sin(P.yaw),fzw=-Math.cos(P.yaw),hsp=Math.hypot(P.vel.x,P.vel.z),back=A.attackAction&&hsp>1&&(P.vel.x*fxw+P.vel.z*fzw)/hsp<-.3;
 A.runDir+=((back?-1:1)-A.runDir)*(1-Math.exp(-9*dt));}
 A.phase=(((A.phase+(rateRun+(rateFast-rateRun)*mix)*dt*A.runDir)%1)+1)%1;
 A.idleT=(A.idleT+dt)%A.durs.Idle;
 A.acts.Idle.time=A.idleT;
 A.acts.Normal_Run.time=A.phase*A.durs.Normal_Run;
 A.acts.Fast_Run.time=((A.phase+ERIKA_FAST_PHASE)%1)*A.durs.Fast_Run;
 A.acts.Jumping.time=A.jt;
 A.acts.Slide.time=A.slideT;
 const wallT=((A.phase+ERIKA_FAST_PHASE)%1)*A.durs.Fast_Run;
 A.acts.Wall_Run_R.time=wallT;A.acts.Wall_Run_L.time=wallT;
 // climbing: the clip's pace follows the real climbing speed (the baked clip rises ~0.63 m per second of playback)
 if(mode==='climb'||mode==='mantle'){const cs=mode==='mantle'?(P.mantle?3.4*(1-erikaSmoothstep(.25,.7,P.mantle.t/P.mantle.dur)):0):erikaClamp(Math.abs(P.vel.y)/ERIKA_CLIMB_MPS,0,6.5);A.climbT=(A.climbT+cs*dt)%A.durs.Climb_Wall;}
 A.acts.Climb_Wall.time=A.climbT;
 A.acts.Hard_Landing.time=Math.min(A.hardT,2.45);
 A.walkAimTime=(A.walkAimTime+dt*erikaClamp(A.sp/4.5,.65,1.35))%A.durs.Walk_Aim;A.acts.Walk_Aim.time=A.walkAimTime;
 // ---- body heading (third person turns toward the direction of travel) and wall-run lean
 let headTarget=0;
 if(thirdPerson&&!flight&&!launching&&mode!=='hard'&&bow.aimW<.05){const vx=P.vel.x,vz=P.vel.z;if(vx*vx+vz*vz>4)headTarget=erikaWrapPi(Math.atan2(-vx,-vz)-P.yaw);if(A.attackAction){if(SWORD_ATK.layered){if(Math.abs(headTarget)>1.88)headTarget=erikaWrapPi(headTarget+Math.PI);headTarget=erikaClamp(headTarget,-.9,.9);}else headTarget=0;}}
 if(thirdPerson&&(mode==='climb'||mode==='mantle'))headTarget=erikaWrapPi(Math.atan2(P.wallNormal.x,P.wallNormal.z)-P.yaw);   // face the wall while climbing
 if(P.slam&&P.slam.super)headTarget=0;
 if(P.lunge||(CHG.down&&CHG.t>LUNGE.charge-.3))headTarget=0;   // charged lunge: the body turns to face the strike   // super strike: the body faces the strike
  A.heading+=erikaWrapPi(headTarget-A.heading)*(1-Math.exp(-10*dt));
 // Wall run (third person): the whole body leans into the wall on top of the clip's own lean (head toward the wall, feet out).
 const wallW=thirdPerson?erikaClamp(A.cur.Wall_Run_R+A.cur.Wall_Run_L,0,1):0,wrSide=2*(A.wallR===undefined?.5:A.wallR)-1;   // +1 = wall on the right of the runner
 const tiltTarget=WALLRUN_POSE.lean*wrSide*wallW;   // roll about the forward axis; wall on the right -> head tilts left (away), feet stay on the wall
 A.tilt+=(tiltTarget-A.tilt)*(1-Math.exp(-9*dt));
 if(playerMesh){playerMesh.rotation.z=A.tilt;lungeSafe(lungeLeanApply);}
 // ---- evaluate, then lay the arm overrides on top
 A.mixer.update(dt);
 if(A.attackAction&&A.attackMove<.5&&A.attackRootPosition&&erikaPlayer&&erikaPlayer.bones.hips)erikaPlayer.bones.hips.position.copy(A.attackRootPosition);
 const wantArm=(A.attackAction&&A.attackWeight>.01)?0:(thirdPerson?((flight||launching||bow.equip>.02)?1:0):1);
 A.armW+=(wantArm-A.armW)*(1-Math.exp(-10*dt));
 if(A.armW>.003)applyErikaArmOverride(A.armW);
 if(wallW>.02)applyWallRunPose(wallW,wrSide);
 if(mode==='mantle'&&P.mantle)applyMantlePose(erikaClamp(P.mantle.t/P.mantle.dur,0,1));
 // ---- archer aiming layer (right mouse): upper-body twist, braced stance, head on target
 const stanceT=(bow.aimW>.01&&(mode==='ground'||mode==='land')&&P.moveSpeed<.65)?1:0;
 A.aimStance=(A.aimStance||0)+(stanceT-(A.aimStance||0))*(1-Math.exp(-9*dt));
 const aimOverlay=bow.aimW*(1-(A.cur.Walk_Aim||0));if(thirdPerson&&A.aim&&A.aim.ready&&aimOverlay>.003)applyErikaAimClip(aimOverlay,A.aimStance,dt);else{A.aimYawOff=0;if(A.aim)A.aim.t=0;}
 if(thirdPerson&&!P.grounded&&(flight||launching)&&bow.equip>.02&&(bow.aiming||bow.drawing))bowAerialLeftHandIK(Math.max(bow.aimW,(bow.aiming||bow.drawing)?0.12:0));
 if(P.slam)slamSafe(slamPoseIK);
 if(P.lunge||LUNGE.pw>.01)lungeSafe(lungePoseIK);
 if(player.kick&&thirdPerson)slamSafe(kickPoseIK);
}
function erikaAdd(bone,x,y,z,w){
 if(!bone||w<.001)return;const T=erikaAnim.tmp;
 T.e.set(x*w,y*w,z*w,'XYZ');T.q.setFromEuler(T.e);bone.quaternion.multiply(T.q);
}
// ---- Bow_Standing_Aim (Mixamo FBX, baked): played in third person while the player aims with the right mouse button.
//  * upper body + arms + fingers always follow the clip; hips + legs follow it too when standing still;
//  * the clip's hip twist is carried onto the spine when the legs keep running/falling;
//  * body yaw and chest pitch are self-calibrated every frame so the bow arm always points down the crosshair.
function setupErikaAim(M,model){
 const node=document.getElementById('erikaAimData');if(!node||!erikaPlayer)return;
 const data=JSON.parse(node.textContent),map={};
 model.traverse(o=>{if(o.isBone)map[o.name]=o;});
 const A={ready:false,n:data.n,fps:data.fps,dur:data.dur,items:[],t:0,yaw:0,pitch:0,hips:map.mixamorigHips,hipsP:new Float32Array(erikaB64(data.hipsP)),
  q1:new M.Quaternion(),q2:new M.Quaternion(),q3:new M.Quaternion(),q4:new M.Quaternion(),axis:new M.Vector3(),v1:new THREE.Vector3(),v2:new THREE.Vector3()};
 for(const name in data.bones){
  const bone=map[name];if(!bone)continue;
  const role=/Hips$/.test(name)?'hips':/Spine$/.test(name)?'spine0':/Spine[12]$/.test(name)?'spine':/(UpLeg|Leg|Foot|ToeBase)$/.test(name)?'leg':'upper';
  A.items.push({bone,role,q:new Float32Array(erikaB64(data.bones[name]))});
 }
 if(!A.hips||!A.items.length)return;
 A.spine0=A.items.find(i=>i.role==='spine0');A.hipsItem=A.items.find(i=>i.role==='hips');
 A.lean=['mixamorigSpine','mixamorigSpine1','mixamorigSpine2'].map((n,i)=>({bone:map[n],f:[.4,.3,.3][i]})).filter(x=>x.bone);
 A.la=map.mixamorigLeftArm;A.lh=map.mixamorigLeftHand;
 A.ready=!!(A.la&&A.lh);erikaAnim.aim=A;node.remove();
}
function erikaAimQ(it,i0,i1,u,out){const a=it.q;out.set(a[i0*4],a[i0*4+1],a[i0*4+2],a[i0*4+3]);const t=erikaAnim.aim.q4.set(a[i1*4],a[i1*4+1],a[i1*4+2],a[i1*4+3]);return out.slerp(t,u);}
function applyErikaAimClip(aw,stance,dt){
 const A=erikaAnim.aim,P=player,bw=aw*stance,aerialBowAim=thirdPerson&&!P.grounded&&(P.state==='GRAPPLING'||P.state==='HOOK LAUNCH'||P.postFlight)&&weapon==='bow'&&(bow.aiming||bow.drawing);
 A.t=Math.min(A.dur,A.t+dt);
 const f=A.t*A.fps,i0=Math.min(A.n-1,Math.floor(f)),i1=Math.min(A.n-1,i0+1),u=f-i0;
 // hips first (legs + hips only when standing)
 const qh=erikaAimQ(A.hipsItem,i0,i1,u,A.q1);
 if(bw>.001){
  A.hips.quaternion.slerp(qh,bw);
  const p=A.hipsP,x=p[i0*3]+(p[i1*3]-p[i0*3])*u,y=p[i0*3+1]+(p[i1*3+1]-p[i0*3+1])*u,z=p[i0*3+2]+(p[i1*3+2]-p[i0*3+2])*u;
  A.hips.position.x+=(x-A.hips.position.x)*bw;A.hips.position.y+=(y-A.hips.position.y)*bw;A.hips.position.z+=(z-A.hips.position.z)*bw;
 }
 const hipsNow=A.q2.copy(A.hips.quaternion);
 for(const it of A.items){
  if(it.role==='hips')continue;if(aerialBowAim&&/Right(?:Arm|ForeArm|Hand)/i.test(it.bone.name))continue;
  const tq=erikaAimQ(it,i0,i1,u,A.q3);
  if(it.role==='leg'){if(bw>.001)it.bone.quaternion.slerp(tq,bw);}
  else if(it.role==='spine0'){
   // keep the chest where the full clip puts it even if the hips stay on the locomotion pose: inv(hips)*clipHips*clipSpine
   tq.premultiply(qh).premultiply(hipsNow.invert());it.bone.quaternion.slerp(tq,aw);
  }else it.bone.quaternion.slerp(tq,aw);
 }
 // chest pitch (rotate about the world right axis, split across the spine chain)
 const lean=A.pitch*aw;
 if(Math.abs(lean)>.001){
  A.axis.set(Math.cos(P.yaw),0,-Math.sin(P.yaw));
  for(const l of A.lean){
   const pq=l.bone.parent.getWorldQuaternion(A.q1);
   const R=A.q2.setFromAxisAngle(A.axis,lean*l.f);
   const delta=A.q3.copy(pq).invert().multiply(R).multiply(pq);
   l.bone.quaternion.premultiply(delta);
  }
 }
 // measure where the bow arm points (in the player's own frame) and steer yaw / pitch towards the crosshair
 playerMesh.updateMatrixWorld(true);
 A.la.getWorldPosition(A.v1);A.lh.getWorldPosition(A.v2);playerMesh.worldToLocal(A.v1);playerMesh.worldToLocal(A.v2);
 const dx=A.v2.x-A.v1.x,dy=A.v2.y-A.v1.y,dz=A.v2.z-A.v1.z,hz=Math.hypot(dx,dz);
 if(aw>.5&&hz>.02){
  const phi=Math.atan2(-dx,-dz),elev=Math.atan2(dy,hz);
  const yawT=erikaWrapPi(-phi-erikaAnim.heading);
  A.yaw+=erikaWrapPi(yawT-A.yaw)*(1-Math.exp(-14*dt));
  A.pitch=erikaClamp(A.pitch+(erikaClamp(P.pitch,-1.15,1.15)-elev)*(1-Math.exp(-10*dt)),-1.2,1.2);
 }else if(aw<=.5)A.pitch*=Math.exp(-8*dt);
 const walkingWhileAiming=P.grounded&&!P.sliding&&P.moveSpeed>.65;
 if(walkingWhileAiming&&Math.abs(A.yaw)>.001){
  A.axis.set(0,1,0);
  for(const l of A.lean){
   const parentQ=l.bone.parent.getWorldQuaternion(A.q1),R=A.q2.setFromAxisAngle(A.axis,A.yaw*aw*l.f);
   const delta=A.q3.copy(parentQ).invert().multiply(R).multiply(parentQ);
   l.bone.quaternion.premultiply(delta);
  }
 }
 erikaAnim.aimYawOff=walkingWhileAiming?0:A.yaw*aw;
}
function animateErikaLegacy(dt){
 if(!erikaPlayer||!erikaPlayer.bones)return;
 const M=erikaModule, b=erikaPlayer.bones, rest=erikaPlayer.rest;
 const state=player.state, speed=player.moveSpeed, moving=player.grounded&&!player.sliding&&speed>.65;
 const sprint=state==='SPRINTING', flight=state==='GRAPPLING'||state==='HOOK LAUNCH'||!!player.postFlight, sliding=player.sliding, wall=player.onWall, airborne=!player.grounded&&!flight;
 const pace=THREE.MathUtils.clamp(speed/(sprint?14:8),0,1), wave=Math.sin(walkBob), waveR=Math.sin(walkBob+Math.PI), alpha=1-Math.exp(-13.5*dt);
 const pose=(key,x=0,y=0,z=0)=>{const bone=b[key];if(!bone)return;const base=rest.get(bone);if(!base)return;const offset=new M.Quaternion().setFromEuler(new M.Euler(x,y,z,'XYZ'));const target=base.clone().multiply(offset);bone.quaternion.slerp(target,alpha);};
 // First person frames the forearms at the bottom edge; third person uses a relaxed, readable full-body pose.
 const lowerPose=thirdPerson?.94:sliding?.4:wall?.30:.62;
 for(const side of [-1,1]){
  const phase=side<0?wave:waveR;
  const armSwing=moving?phase*(sprint?.34:.22)*pace:0;
  const armDown=flight?(thirdPerson?-.08:.02):sliding?-.26:wall?.35:airborne?-.08:(thirdPerson?(moving?.88:lowerPose):lowerPose);
  const armForward=flight?(thirdPerson?.86:1.05):sliding?-.20:wall?.35:moving?(thirdPerson?.10:.36):(thirdPerson?.02:.28);
  const shoulderX=flight?-.20:sliding?.16:wall?.10:airborne?-.16:0;
  const shoulderZ=(side<0?1:-1)*(armDown+armSwing*(side<0?1:-1));
  pose(side<0?'leftArm':'rightArm',shoulderX, (side<0?-1:1)*armForward, shoulderZ);
  const elbowBend=flight?.30:sliding?.58:wall?.22:airborne?.48:moving?(sprint?.16:.10)+Math.max(0,-phase)*.27:.12;
  pose(side<0?'leftForeArm':'rightForeArm',-elbowBend,0,(side<0?1:-1)*(flight?.05:.025));
  pose(side<0?'leftHand':'rightHand',flight?-.10:0,(side<0?1:-1)*(flight?.05:.015),0);
  const step=side<0?wave:waveR;
  const legSwing= moving?step*(sprint?.54:.38)*pace:flight?-.20:sliding?.72:wall?step*.48:airborne?-.18:Math.sin(elapsed*1.7+side)*.012;
  pose(side<0?'leftUpLeg':'rightUpLeg',legSwing,0,(side<0?-1:1)*(wall?.12:0));
  const kneeBend=flight?.64:sliding?1.05:wall?.48:airborne?.52:moving?Math.max(0,-step)*(sprint?.72:.55)*pace:.035;
  pose(side<0?'leftLeg':'rightLeg',kneeBend,0,0);
  pose(side<0?'leftFoot':'rightFoot',flight?-.18:moving?-legSwing*.20:airborne?-.08:0,0,0);
 }
 const forwardLean=flight?-.26:sprint?-.16:moving?-.075*pace:sliding?-.28:wall?-.12:airborne?(player.vel.y>1?.04:.12):Math.sin(elapsed*1.7)*.008;
 const sideLean=wall?-player.wallSide*.13:flight?THREE.MathUtils.clamp(player.vel.x*.006,-.10,.10):0;
 pose('hips',forwardLean*.18,0,sideLean*.35);pose('spine',forwardLean*.55,0,sideLean*.5);pose('spine1',forwardLean*.30,0,sideLean*.35);pose('spine2',forwardLean*.15,0,sideLean*.15);
}
function applyCharacterViewMode(){
 if(!erikaPlayer)return;
 // Keep the complete FBX character intact for third person; collapse head skin bones only while the camera is first person.
 for(const [bone,restScale] of erikaPlayer.headScales||[]){
  if(thirdPerson)bone.scale.copy(restScale);else bone.scale.set(restScale.x*.0001,restScale.y*.0001,restScale.z*.0001);
 }
 for(const obj of erikaPlayer.eyeObjects||[])obj.visible=thirdPerson&&obj.userData.erikaEyeOriginalVisible!==false;
 // First person: nudge the body slightly back so the camera never sits inside the pelvis.
 if(erikaPlayer.root&&typeof erikaPlayer.baseZ==="number")erikaPlayer.root.position.z=erikaPlayer.baseZ+(thirdPerson?0:.1);
}
async function loadErikaPlayer(){
 const dataNode=document.getElementById('erikaFbxData');
 if(!dataNode)throw new Error('Embedded Erika FBX data is missing');
 ui.loadtext.textContent='Loading Erika Archer model and materials';ui.loadbar.style.width='76%';
 const [M,loaderModule]=await Promise.all([
  import('three'),
  import('./vendor/three/examples/jsm/loaders/FBXLoader.js')
 ]);
 erikaModule=M;
 const manager=new M.LoadingManager();let textureDoneResolve;
 const textureDone=new Promise(resolve=>{textureDoneResolve=resolve;});manager.onLoad=()=>textureDoneResolve();manager.onError=(url)=>console.warn('Erika texture failed to load:',url);
 const loader=new loaderModule.FBXLoader(manager);const source=dataNode.textContent.trim();
 const buffer=new TextEncoder().encode(source).buffer;
 const model=loader.parse(buffer,'');model.name='ErikaArcher_MainCharacter';
 model.updateMatrixWorld(true);
 const initialBounds=new M.Box3().setFromObject(model);const size=initialBounds.getSize(new M.Vector3());
 if(!Number.isFinite(size.y)||size.y<.05)throw new Error('Erika model has invalid dimensions');
 model.scale.setScalar(1.78/size.y);model.rotation.y=Math.PI;model.updateMatrixWorld(true);
 const fittedBounds=new M.Box3().setFromObject(model);const center=fittedBounds.getCenter(new M.Vector3());
 model.position.x-=center.x;model.position.z-=center.z;model.position.y-=fittedBounds.min.y;
 model.updateMatrixWorld(true);
 model.traverse(obj=>{
  const name=erikaNormName(obj.name);
  if(obj.isSkinnedMesh){obj.castShadow=false;obj.receiveShadow=false;obj.frustumCulled=false;}
  if(name.includes('eyelash')||name.includes('eyemesh')||name.includes('eyesmesh')||name==='eyes'||name==='eyelashes'){
   obj.userData.erikaEyeDetail=true;obj.userData.erikaEyeOriginalVisible=obj.visible;obj.visible=false;
  }
  if(obj.material){const list=Array.isArray(obj.material)?obj.material:[obj.material];for(const material of list){for(const key of ['color','emissive','specular']){const c=material[key];if(c&&!(Number.isFinite(c.r)&&Number.isFinite(c.g)&&Number.isFinite(c.b)&&c.r<=1&&c.g<=1&&c.b<=1))c.set(key==='color'?0xffffff:key==='emissive'?0x000000:0x222222);}if(material.map)material.map.colorSpace=M.SRGBColorSpace;material.needsUpdate=true;}}
 });
 // Replace the old procedural ninja body only after the custom model parses successfully.
 playerMesh.add(model);
 if(torso)torso.visible=false;for(const l of legs)if(l.leg)l.leg.visible=false;
 const boneMap={};model.traverse(obj=>{if(obj.isBone){const n=erikaNormName(obj.name);if(!boneMap[n])boneMap[n]=obj;}});
 const findBone=suffix=>{const needle=erikaNormName(suffix);for(const [n,bone] of Object.entries(boneMap))if(n.endsWith(needle))return bone;return null;};
 const bones={
  hips:findBone('hips'),spine:findBone('spine'),spine1:findBone('spine1'),spine2:findBone('spine2'),head:findBone('head'),neck:findBone('neck'),
  leftArm:findBone('leftarm'),rightArm:findBone('rightarm'),leftForeArm:findBone('leftforearm'),rightForeArm:findBone('rightforearm'),
  leftHand:findBone('lefthand'),rightHand:findBone('righthand'),leftUpLeg:findBone('leftupleg'),rightUpLeg:findBone('rightupleg'),
  leftLeg:findBone('leftleg'),rightLeg:findBone('rightleg'),leftFoot:findBone('leftfoot'),rightFoot:findBone('rightfoot')
 };
 const rest=new Map();for(const bone of Object.values(bones))if(bone)rest.set(bone,bone.quaternion.clone());
 const headBones=Object.entries(boneMap).filter(([n])=>n.endsWith('head')||n.includes('headtop')||n.includes('lefteye')||n.includes('righteye')||n.endsWith('jaw')||n.endsWith('teeth')||n.endsWith('ear')).map(([,bone])=>bone);
 const headScales=new Map(headBones.map(bone=>[bone,bone.scale.clone()]));
 const eyeObjects=[];model.traverse(obj=>{if(obj.userData.erikaEyeDetail)eyeObjects.push(obj);});
 erikaPlayer={root:model,bones,rest,headBones,headScales,eyeObjects,baseZ:model.position.z};
 playerMesh.updateMatrixWorld(true);const rootRestQ=playerMesh.getWorldQuaternion(new M.Quaternion()),hipsRestQ=bones.hips?bones.hips.getWorldQuaternion(new M.Quaternion()):rootRestQ.clone(),invHipsRestQ=hipsRestQ.clone().invert();
 const rootOffsetToHip=(x,y,z)=>new M.Vector3(x,y,z).applyQuaternion(rootRestQ).applyQuaternion(invHipsRestQ);
 erikaPlayer.hipOffsets={left:rootOffsetToHip(-.2,.03,-.03),right:rootOffsetToHip(.2,.03,-.03)};
 erikaPlayer.hipRootRotation=invHipsRestQ.clone().multiply(rootRestQ);
 const backBone=bones.spine2||bones.spine||bones.hips,backRestPos=backBone?backBone.getWorldPosition(new M.Vector3()):playerMesh.getWorldPosition(new M.Vector3()),backRestQ=backBone?backBone.getWorldQuaternion(new M.Quaternion()):rootRestQ.clone(),hipsRestPos=bones.hips?bones.hips.getWorldPosition(new M.Vector3()):playerMesh.getWorldPosition(new M.Vector3());
 const desiredBackPos=hipsRestPos.add(new M.Vector3(.04,.5,.5).applyQuaternion(rootRestQ));erikaPlayer.backBone=backBone;erikaPlayer.backOffset=desiredBackPos.sub(backRestPos).applyQuaternion(backRestQ.clone().invert());
 erikaPlayer.backRotation=backRestQ.clone().invert().multiply(rootRestQ).multiply(new M.Quaternion().setFromEuler(new M.Euler(0,0,-.55)));
 setupErikaFPMask(model);
 applyCharacterViewMode();
 
 // The FBX has a short near-static source take; in-game movement is driven by state-aware skeletal poses.
 setupErikaAnimations(M,model,loader);try{await loadMonsterModels(M,loaderModule);}catch(error){console.warn('Monster models unavailable; keeping the procedural monsters.',error);}try{await loadCaptiveModel(M,loaderModule);}catch(error){console.warn('Captive model unavailable; keeping the procedural captive.',error);}erikaLoaded=true;playerMesh.updateMatrixWorld(true);animateErika(1/60);
 try{await Promise.race([textureDone,new Promise(resolve=>setTimeout(resolve,12000))]);}catch(e){}
 dataNode.remove();
 console.info('Erika Archer loaded as the main character.',{height:size.y,embeddedTextures:5,bones:Object.values(bones).filter(Boolean).length});
 return true;
}
const CABLE_GEO=new THREE.CylinderGeometry(.042,.042,1,10,1,false);
const _cabDir=new THREE.Vector3(),_cabUp=new THREE.Vector3(0,1,0);
function setCableSegment(mesh,a,b){_cabDir.subVectors(b,a);const len=_cabDir.length();if(len<.001){mesh.visible=false;return;}_cabDir.multiplyScalar(1/len);mesh.position.addVectors(a,b).multiplyScalar(.5);mesh.scale.set(1,len,1);mesh.quaternion.setFromUnitVectors(_cabUp,_cabDir);}
function buildHookVisuals(){for(const h of hooks){const line=new THREE.Mesh(CABLE_GEO,new THREE.MeshStandardMaterial({color:0x34373c,roughness:.62,metalness:.35}));line.frustumCulled=false;line.visible=false;scene.add(line);h.line=line;const tip=new THREE.Mesh(new THREE.SphereGeometry(.13,8,6),mats.metal);tip.visible=false;scene.add(tip);h.tip=tip;const hookBody=new THREE.Mesh(new THREE.ConeGeometry(.14,.42,6),mats.metal);hookBody.rotation.x=-Math.PI/2;hookBody.visible=false;scene.add(hookBody);h.mesh=hookBody;}}
function cameraDir(){const d=new THREE.Vector3();camera.getWorldDirection(d);return d.normalize();}
function getHandWorld(side){
 // Cable origin = the grapple launchers on the hips (left / right of the waist), NOT the hands,
 // so both hands stay free for the bow while flying.
 const p=new THREE.Vector3();
 if(playerMesh){
  playerMesh.updateMatrixWorld(true);
  const hips=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.hips;
  if(hips){hips.getWorldPosition(p);hips.getWorldQuaternion(_hipQ);const local=erikaPlayer.hipOffsets&&erikaPlayer.hipOffsets[side<0?'left':'right'];if(local)return p.add(_hipOff.copy(local).applyQuaternion(_hipQ));}
  else{p.set(0,.98,0).applyMatrix4(playerMesh.matrixWorld);playerMesh.getWorldQuaternion(_hipQ);}
  _hipOff.set(side*.2,.03,-.03).applyQuaternion(_hipQ);
  return p.add(_hipOff);
 }
 const local=new THREE.Vector3(side*.2,.98,-.03);local.applyAxisAngle(new THREE.Vector3(0,1,0),player.yaw);local.add(player.pos);return local;
}
function showToast(text){}   // on-screen messages removed

const AUDIO_DATA={"monster": "assets/audio/monster.mp3", "monsterDie": "assets/audio/monsterDie.mp3", "bow": "assets/audio/bow.mp3", "run": "assets/audio/run.mp3", "swordGround": "assets/audio/swordGround.mp3", "swordHit": "assets/audio/swordHit.mp3"};
const audioSettings={master:.8,music:.55,effects:.85,muted:false};
const MENU_MUSIC_DATA='assets/audio/menu_music.mp3';
const menuMusic=new Audio(MENU_MUSIC_DATA);menuMusic.loop=true;menuMusic.preload='auto';
let menuMusicRequested=false;
let musicGameplayMode=false;
const GAMEPLAY_MUSIC_MULTIPLIER=.28; // 28% of menu volume while playing.
function syncMenuMusic(){
 const stateVolume=musicGameplayMode?GAMEPLAY_MUSIC_MULTIPLIER:1;
 menuMusic.volume=THREE.MathUtils.clamp(audioSettings.master*audioSettings.music*stateVolume,0,1);
 const audible=!audioSettings.muted&&audioSettings.master>0&&audioSettings.music>0;
 if(menuMusicRequested&&audible){if(menuMusic.paused){const p=menuMusic.play();if(p&&p.catch)p.catch(()=>{});}}
 else if(!menuMusic.paused)menuMusic.pause();
}
function startMenuMusic(){menuMusicRequested=true;musicGameplayMode=false;syncMenuMusic();}
function startGameplayMusic(){menuMusicRequested=true;musicGameplayMode=true;syncMenuMusic();}
function stopMenuMusic(){menuMusicRequested=false;syncMenuMusic();}
const audioPlayers={},audioTemplates={};
// Supplied captive-under-attack warning recording (embedded so the game remains a single HTML file).
const CAPTIVE_WARNING_AUDIO='assets/audio/captive_warning.mp3';
const captiveWarningPlayers=new Set();let captiveWarningTemplate=null;
function playCaptiveWarning(){
 if(audioSettings.muted||audioSettings.master*audioSettings.effects<=0)return null;
 const a=captiveWarningTemplate?captiveWarningTemplate.cloneNode(true):new Audio(CAPTIVE_WARNING_AUDIO);
 a.preload='auto';a.loop=false;a.volume=THREE.MathUtils.clamp(audioSettings.master*audioSettings.effects,0,1);
 try{a.currentTime=0;}catch(e){}
 captiveWarningPlayers.add(a);
 a.addEventListener('ended',()=>captiveWarningPlayers.delete(a),{once:true});
 const p=a.play();if(p&&p.catch)p.catch(()=>captiveWarningPlayers.delete(a));
 return a;
}
const activeMonsterAudio=new Set();
let runFootsteps=null;
function loadAudioSettings(){
 try{const v=JSON.parse(localStorage.getItem('attackCityAudioSettings')||'{}');if(Number.isFinite(v.master))audioSettings.master=THREE.MathUtils.clamp(v.master,0,1);if(Number.isFinite(v.music))audioSettings.music=THREE.MathUtils.clamp(v.music,0,1);if(Number.isFinite(v.effects))audioSettings.effects=THREE.MathUtils.clamp(v.effects,0,1);audioSettings.muted=!!v.muted;}catch(e){}
 applyAudioSettingsUI();
}
function saveAudioSettings(){try{localStorage.setItem('attackCityAudioSettings',JSON.stringify(audioSettings));}catch(e){}}
function applyAudioSettingsUI(){
 const m=document.getElementById('masterVolume'),mu=document.getElementById('musicVolume'),e=document.getElementById('effectsVolume'),q=document.getElementById('muteAudio');
 if(m)m.value=audioSettings.master;if(mu)mu.value=audioSettings.music;if(e)e.value=audioSettings.effects;if(q)q.checked=audioSettings.muted;
 syncMenuMusic();
 Object.values(audioPlayers).forEach(a=>a.volume=audioSettings.muted?0:audioSettings.master*audioSettings.effects);
 captiveWarningPlayers.forEach(a=>a.volume=audioSettings.muted?0:audioSettings.master*audioSettings.effects);
 updateMonsterAudioVolumes();
 if(runFootsteps)runFootsteps.volume=audioSettings.muted?0:audioSettings.master*audioSettings.effects;
}
function monsterDistanceVolume(monster){
 if(!monster||!monster.root||!player||!player.pos)return 0;
 const dx=monster.root.position.x-player.pos.x,dz=monster.root.position.z-player.pos.z;
 const dy=(monster.root.position.y||0)-(player.pos.y||0);
 const d=Math.sqrt(dx*dx+dy*dy+dz*dz);
 // Monster sounds peak at half their former volume nearby, then fade smoothly with distance.
 const t=THREE.MathUtils.clamp((d-3)/(42-3),0,1);
 const attenuation=1-(t*t*(3-2*t));
 return .5*attenuation;
}
function updateMonsterAudioVolumes(){
 const base=audioSettings.muted?0:audioSettings.master*audioSettings.effects;
 for(const item of activeMonsterAudio){
  const a=item.audio,m=item.monster;
  if(!a||a.paused||a.ended){activeMonsterAudio.delete(item);continue;}
  a.volume=THREE.MathUtils.clamp(base*monsterDistanceVolume(m),0,1);
 }
}
function playMonsterAsset(key,monster){
 if(audioSettings.muted||audioSettings.master*audioSettings.effects<=0)return null;
 const a=getAudio(key,false),item={audio:a,monster};
 a.volume=THREE.MathUtils.clamp(audioSettings.master*audioSettings.effects*monsterDistanceVolume(monster),0,1);
 activeMonsterAudio.add(item);
 a.addEventListener('ended',()=>activeMonsterAudio.delete(item),{once:true});
 a.play().catch(()=>activeMonsterAudio.delete(item));
 return a;
}
const audioPool={};
function getAudio(key,loop=false){
 const vol=audioSettings.muted?0:audioSettings.master*audioSettings.effects;
 if(loop){const a=audioTemplates[key]?audioTemplates[key].cloneNode(true):new Audio(AUDIO_DATA[key]);a.preload='auto';a.loop=true;a.volume=vol;return a;}
 const P=audioPool[key]||(audioPool[key]={i:0,list:Array.from({length:5},()=>{const a=new Audio(AUDIO_DATA[key]);a.preload='auto';return a;})});
 const a=P.list[P.i++%P.list.length];try{a.pause();a.currentTime=0;}catch(e){}a.loop=false;a.volume=vol;return a;
}
function playAsset(key,loop=false){
 if(audioSettings.muted||audioSettings.master*audioSettings.effects<=0)return null;
 if(loop){
  if(!runFootsteps){runFootsteps=getAudio(key,true);runFootsteps.play().catch(()=>{});}
  else if(runFootsteps.paused){runFootsteps.currentTime=0;runFootsteps.play().catch(()=>{});}
  return runFootsteps;
 }
 const a=getAudio(key,false);audioPlayers[key]=a;a.play().catch(()=>{});a.addEventListener('ended',()=>{if(audioPlayers[key]===a)delete audioPlayers[key];},{once:true});return a;
}
function stopRunFootsteps(){if(runFootsteps){runFootsteps.pause();runFootsteps.currentTime=0;}}
function initAudioSettingsUI(){
 loadAudioSettings();
 for(const [id,key] of [['masterVolume','master'],['musicVolume','music'],['effectsVolume','effects']]){
  const el=document.getElementById(id);if(el)el.addEventListener('input',()=>{audioSettings[key]=Number(el.value);applyAudioSettingsUI();saveAudioSettings();});
 }
 const mute=document.getElementById('muteAudio');if(mute)mute.addEventListener('change',()=>{audioSettings.muted=mute.checked;applyAudioSettingsUI();saveAudioSettings();});
 // Warm the browser's media cache before gameplay; playback is still triggered only by game events.
 Object.keys(AUDIO_DATA).forEach(k=>{const a=new Audio(AUDIO_DATA[k]);a.preload='auto';a.load();audioTemplates[k]=a;});
  captiveWarningTemplate=new Audio(CAPTIVE_WARNING_AUDIO);captiveWarningTemplate.preload='auto';captiveWarningTemplate.load();
 menuMusic.load();startMenuMusic();
 const unlockMenuMusic=()=>{if(menuMusicRequested)syncMenuMusic();};
 document.addEventListener('pointerdown',unlockMenuMusic,true);document.addEventListener('keydown',unlockMenuMusic,true);
 runFootsteps=getAudio('run',true);runFootsteps.load();
}
function playAssetNow(key){
 const a=playAsset(key,false);return a;
}
// ===================== REALISTIC SFX V2 (procedural Web Audio): jump voice, landing, cable/rope, wind while falling, charged-strike power-up =====================
// Everything is synthesised live (no extra files). All of it follows the Master / Effects / Mute sliders in the settings menu.
const SFX_JUMP_DATA=["assets/audio/sfx_jump_0.mp3", "assets/audio/sfx_jump_1.mp3", "assets/audio/sfx_jump_2.mp3"];   // real recorded female jump grunts (3 variations)
const SFX={capT:0,jb:[],jl:-1,ctx:null,out:null,white:null,pink:null,last:{},wind:null,rope:null,chg:null,pLunge:false,pReady:false,pChg:false};
const sfxCl=(v,a,b)=>Math.max(a,Math.min(b,v));
const sfxSm=(a,b,v)=>{const t=sfxCl((v-a)/(b-a),0,1);return t*t*(3-2*t);};
function sfxVol(){return audioSettings.muted?0:audioSettings.master*audioSettings.effects;}
function sfxInit(ctxOverride){
 if(SFX.ctx)return true;
 let ac=ctxOverride||audioCtx;
 if(!ac){ac=new (window.AudioContext||window.webkitAudioContext)();audioCtx=ac;}
 SFX.ctx=ac;SFX.gw=null;
 const comp=ac.createDynamicsCompressor();comp.threshold.value=-16;comp.knee.value=18;comp.ratio.value=5;comp.attack.value=.004;comp.release.value=.2;
 const out=ac.createGain();out.gain.value=sfxVol();out.connect(comp);comp.connect(ac.destination);SFX.out=out;
 const shot=ac.createGain();shot.gain.value=2.2;shot.connect(out);SFX.shot=shot;   // one-shots bus (makeup gain)
 const sr=ac.sampleRate,w=ac.createBuffer(1,sr*2,sr),wd=w.getChannelData(0);
 for(let i=0;i<wd.length;i++)wd[i]=Math.random()*2-1;
 const p=ac.createBuffer(1,sr*3,sr),pd=p.getChannelData(0);let b0=0,b1=0,b2=0,b3=0,b4=0,b5=0,b6=0;   // pink noise (Paul Kellet): softer, more natural than white
 for(let i=0;i<pd.length;i++){const x=Math.random()*2-1;b0=.99886*b0+x*.0555179;b1=.99332*b1+x*.0750759;b2=.969*b2+x*.153852;b3=.8665*b3+x*.3104856;b4=.55*b4+x*.5329522;b5=-.7616*b5-x*.016898;pd[i]=(b0+b1+b2+b3+b4+b5+b6+x*.5362)*.11;b6=x*.115926;}
 SFX.white=w;SFX.pink=p;
 SFX.jb=[];try{SFX_JUMP_DATA.forEach((u,i)=>{fetch(u).then(r=>r.arrayBuffer()).then(ab=>{
  const r=ac.decodeAudioData(ab,b=>{SFX.jb[i]=b;},()=>{});if(r&&r.catch)r.catch(()=>{});}).catch(()=>{});});}catch(e){}   // decode once; played back by sfxJump
 return true;
}
function sfxReady(){
 try{
  if(!SFX.ctx&&!sfxInit())return false;
  const ac=SFX.ctx;
  if(ac.state==='suspended'&&ac.resume){try{const r=ac.resume();if(r&&r.catch)r.catch(()=>{});}catch(e){}}
  const v=sfxVol();if(v<=0)return false;
  SFX.out.gain.setTargetAtTime(v,ac.currentTime,.02);return true;
 }catch(e){return false;}
}
// ---- building blocks ----
function sfxNoise(t0,dur,pink){const s=SFX.ctx.createBufferSource();s.buffer=pink?SFX.pink:SFX.white;s.loop=true;s.start(t0,Math.random()*1.5);s.stop(t0+dur+.05);return s;}
function sfxEnv(g,t0,peak,att,dur){const F=.0001;g.gain.setValueAtTime(F,t0);g.gain.exponentialRampToValueAtTime(Math.max(F*2,peak),t0+att);g.gain.exponentialRampToValueAtTime(F,t0+dur);}
function sfxBurst(t0,dur,type,f0,f1,q,peak,att,pink,dest){
 const ac=SFX.ctx,n=sfxNoise(t0,dur,pink),f=ac.createBiquadFilter(),g=ac.createGain();
 f.type=type;f.Q.value=q;f.frequency.setValueAtTime(f0,t0);f.frequency.exponentialRampToValueAtTime(Math.max(20,f1),t0+dur);
 sfxEnv(g,t0,peak,Math.min(att||.01,dur*.5),dur);n.connect(f);f.connect(g);g.connect(dest||SFX.shot);
}
function sfxTone(t0,type,f0,f1,dur,peak,att,dest){
 const ac=SFX.ctx,o=ac.createOscillator(),g=ac.createGain();
 o.type=type;o.frequency.setValueAtTime(f0,t0);o.frequency.exponentialRampToValueAtTime(Math.max(20,f1),t0+dur);
 sfxEnv(g,t0,peak,Math.min(att||.005,dur*.5),dur);o.connect(g);g.connect(dest||SFX.shot);o.start(t0);o.stop(t0+dur+.05);
}
// human voice: sawtooth "vocal cords" through three formant filters (vowel) + a little breath noise
function sfxVoice(t0,o){
 const ac=SFX.ctx,V={a:[850,1220,2810],o:[500,900,2700],u:[380,900,2600],e:[600,2050,2900]},F=V[o.vowel||'a'],dur=o.dur;
 const src=ac.createOscillator(),out=ac.createGain();
 src.type='sawtooth';src.frequency.setValueAtTime(o.f0,t0);src.frequency.exponentialRampToValueAtTime(o.f1,t0+dur);
 const lfo=ac.createOscillator(),lg=ac.createGain();lfo.frequency.value=5.5+Math.random()*1.5;lg.gain.value=o.f0*.012;lfo.connect(lg);lg.connect(src.frequency);lfo.start(t0);lfo.stop(t0+dur+.05);   // faint natural pitch wobble
 sfxEnv(out,t0,o.gain,o.att||.02,dur);
 F.forEach((fr,i)=>{const bp=ac.createBiquadFilter(),g=ac.createGain();bp.type='bandpass';bp.frequency.value=fr*(o.shift||1);bp.Q.value=[7,9,11][i];g.gain.value=[1,.65,.3][i];src.connect(bp);bp.connect(g);g.connect(out);});
 if(o.breath){const n=sfxNoise(t0,dur,false),bp=ac.createBiquadFilter(),g=ac.createGain();bp.type='bandpass';bp.frequency.value=F[1];bp.Q.value=1.2;g.gain.value=o.breath;n.connect(bp);bp.connect(g);g.connect(out);}
 out.connect(SFX.shot);src.start(t0);src.stop(t0+dur+.05);
}

// realistic voice: glottal-pulse source (periodic wave, -12 dB/oct) -> 3 gliding formants, aspirated "h" onset, pitch jitter, abrupt glottal stop
function sfxGlottal(){
 if(SFX.gw)return SFX.gw;const N=48,re=new Float32Array(N+1),im=new Float32Array(N+1);
 for(let n=1;n<=N;n++)im[n]=(1/Math.pow(n,1.6))*(1+.25*Math.sin(n*1.7));
 SFX.gw=SFX.ctx.createPeriodicWave(re,im);return SFX.gw;
}
function sfxVoice2(t0,o){
 const ac=SFX.ctx,asp=o.asp||0,vt=t0+asp*.55,vdur=o.dur-asp*.55;
 const inp=ac.createGain(),out=ac.createGain(),lp=ac.createBiquadFilter();lp.type='lowpass';lp.frequency.value=6500;
 const src=ac.createOscillator();src.setPeriodicWave(sfxGlottal());
 const N=28,cv=new Float32Array(N);
 for(let i=0;i<N;i++){const u=i/(N-1);cv[i]=o.f0*(1+(o.rise||.07)*Math.sin(Math.PI*Math.min(1,u*1.7))-(o.fall||.2)*u*u)*(1+(Math.random()-.5)*.035);}   // contour + jitter
 src.frequency.setValueCurveAtTime(cv,vt,vdur);
 const vg=ac.createGain();vg.gain.setValueAtTime(.0001,vt);vg.gain.exponentialRampToValueAtTime(o.gain,vt+.022);vg.gain.setValueAtTime(o.gain,vt+vdur*(o.hold||.55));vg.gain.exponentialRampToValueAtTime(.0001,vt+vdur);
 src.connect(vg);vg.connect(inp);
 const nz=sfxNoise(t0,o.dur,false),ng=ac.createGain();   // aspiration (the breathy "h") fading into a little breath under the vowel
 ng.gain.setValueAtTime(.0001,t0);ng.gain.exponentialRampToValueAtTime(o.aspGain||.5,t0+.012);ng.gain.exponentialRampToValueAtTime(o.breath||.08,t0+Math.max(.03,asp));ng.gain.exponentialRampToValueAtTime(.0001,t0+o.dur);
 nz.connect(ng);ng.connect(inp);
 const Q=[9,13,16],G=[1,.75,.4];
 for(let i=0;i<3;i++){const bp=ac.createBiquadFilter(),g=ac.createGain();bp.type='bandpass';bp.Q.value=Q[i];bp.frequency.setValueAtTime(o.f1[i],t0);bp.frequency.linearRampToValueAtTime(o.f2[i],t0+o.dur*.75);g.gain.value=G[i]*(o.fs||1);inp.connect(bp);bp.connect(g);g.connect(out);}
 const lo=ac.createBiquadFilter();lo.type='lowshelf';lo.frequency.value=400;lo.gain.value=4;   // chest warmth
 out.connect(lo);lo.connect(lp);lp.connect(SFX.shot);src.start(vt);src.stop(vt+vdur+.05);
}
function sfxCaptiveAlarm(){playCaptiveWarning();}   // supplied recording: captive being attacked

function sfxBell(t,f,dur,peak){sfxTone(t,'sine',f,f,dur,peak,.004);sfxTone(t,'sine',f*2.01,f*2.01,dur*.6,peak*.35,.003);sfxTone(t,'sine',f*3.98,f*3.98,dur*.3,peak*.15,.002);}
function sfxLevelUp(){   // rising bell arpeggio + warm swell + sparkle: "you levelled up"
 const t=SFX.ctx.currentTime+.01;
 [523.25,659.25,783.99,1046.5].forEach((f,i)=>sfxBell(t+i*.085,f,.9+i*.08,.2));
 [1046.5,1318.5,1568].forEach(f=>sfxBell(t+.36,f,1.5,.15));
 sfxTone(t,'sawtooth',130,520,.9,.09,.15);
 sfxTone(t,'sine',110,55,.5,.5,.004);
 sfxBurst(t,.5,'bandpass',500,4000,1.2,.18,.15);
 sfxBurst(t+.3,1,'highpass',5000,9000,.7,.07,.2);
}
function sfxUpgrade(){   // upgrade bought: forge "clink" + bright two-note power-up chime + rising shimmer
 const t=SFX.ctx.currentTime+.005;
 sfxBurst(t,.07,'highpass',3000,8000,.8,.3,.002);
 [1900,2850,3800].forEach((f,i)=>sfxTone(t,'sine',f,f*.995,.45-i*.1,.11,.002));
 sfxTone(t,'triangle',180,90,.22,.4,.004);
 sfxBell(t+.07,783.99,.7,.2);sfxBell(t+.17,1174.7,1,.22);sfxBell(t+.17,1568,1.1,.1);
 sfxTone(t+.05,'sawtooth',300,900,.4,.06,.08);
 sfxBurst(t+.2,.5,'highpass',6000,10000,.7,.07,.15);
}
function sfxBlock(){   // guard raised (Q): steel shing + energy-shield whomp + short blue hum
 const t=SFX.ctx.currentTime+.003;
 sfxBurst(t,.18,'highpass',2800,6500,.8,.28,.004);
 [2800,4200,5600].forEach((f,i)=>sfxTone(t,'sine',f,f*.99,.4-i*.08,.1,.002));
 sfxTone(t+.03,'sine',210,80,.28,.55,.006);
 sfxBurst(t+.03,.3,'bandpass',400,1800,1.4,.2,.1,true);
 sfxTone(t+.05,'triangle',196,262,.5,.13,.06);sfxTone(t+.05,'sine',392,524,.5,.1,.06);
 sfxBurst(t,.25,'bandpass',1200,500,.9,.07,.04,true);
}
// ---- one-shot sounds ----
function sfxJump(){
 const ac=SFX.ctx,t=ac.currentTime+.005,r=()=>.92+Math.random()*.16;
 sfxTone(t,'sine',150*r(),52,.12,.25,.004);                                   // push-off thud
 sfxBurst(t,.07,'lowpass',1900,300,.7,.15,.004,true);                         // shoe scuff on the surface
 const ready=SFX.jb.map((b,i)=>b?i:-1).filter(i=>i>=0);
 if(ready.length){                                                            // the real recorded voice (never the same clip twice in a row)
  let k=ready[Math.floor(Math.random()*ready.length)];if(ready.length>1&&k===SFX.jl)k=ready[(ready.indexOf(k)+1)%ready.length];SFX.jl=k;
  const s=ac.createBufferSource(),g=ac.createGain();s.buffer=SFX.jb[k];s.playbackRate.value=.96+Math.random()*.08;g.gain.value=.6;s.connect(g);g.connect(SFX.shot);s.start(t);return;
 }
 const f=228+Math.random()*30,kk=Math.random(),v=kk<.4?
  {asp:.05,dur:.2,f1:[700,1250,2750],f2:[790,1320,2800],hold:.5}:
  kk<.75?{asp:.06,dur:.27,f1:[800,1300,2800],f2:[860,1220,2800],hold:.6}:
  {asp:.04,dur:.25,f1:[450,2150,3000],f2:[850,1250,2800],hold:.55};
 sfxVoice2(t+.01,Object.assign({f0:f,rise:.08,fall:.22,gain:.6,aspGain:.5,breath:.1,fs:1.6},v));   // fallback if decoding failed
}
function sfxLand(fall){
 if(fall<3)return;if(!sfxReady())return;
 const ac=SFX.ctx,t=ac.currentTime+.003,k=sfxCl((fall-3)/24,0,1),r=()=>.93+Math.random()*.14;
 sfxTone(t,'sine',(120+40*(1-k))*r(),34,.16+.2*k,.3+.5*k,.003);              // body impact
 sfxBurst(t,.06+.08*k,'lowpass',1600,160,.7,.25+.3*k,.002,true);              // heavy foot-fall
 sfxBurst(t,.03,'bandpass',2300*r(),1500,1.4,.1+.12*k,.001,false);            // sharp contact click (shoe on stone)
 sfxBurst(t+.03,.22+.2*k,'bandpass',1100,500,.8,.06+.07*k,.04,true);          // clothes rustle
 if(k>.2)sfxVoice(t+.015,{f0:210*r(),f1:135,dur:.14+.2*k,gain:.1+.28*k,vowel:'o',breath:.45,att:.015});   // exhale "hnf" -> "oof"
 if(k>.55){sfxTone(t,'sine',62,26,.7,.55*k,.004);sfxBurst(t+.04,.5,'lowpass',420,60,.6,.3*k,.01,true);for(let i=0;i<5;i++)sfxBurst(t+.08+i*.045+Math.random()*.03,.03,'highpass',3500,5200,.8,.05*k,.001);}   // shockwave + debris
}

function sfxMonsterHurt(){
 const t=SFX.ctx.currentTime+.003;
 // One fixed body-hit signature for every damaging weapon: dense thud + short organic groan.
 sfxTone(t,'sine',112,43,.22,.30,.002);                                // low body impact
 sfxBurst(t,.13,'lowpass',760,95,.82,.34,.002,true);                   // heavy, dull flesh/body thump
 sfxBurst(t+.006,.085,'bandpass',1380,420,1.05,.17,.001);              // compact impact crack (not a weapon sound)
 sfxVoice(t+.012,{f0:132,f1:68,dur:.17,gain:.17,vowel:'o',breath:.22,att:.009}); // restrained guttural hurt grunt
}
function sfxHookFire(){
 const t=SFX.ctx.currentTime+.004;
 // Mechanical launcher: safety catch / trigger, compressed-gas punch, then a fast cable spool-out.
 sfxBurst(t,.028,'highpass',3900,2100,2.2,.24,.001);                  // hard metal trigger click
 sfxTone(t,'triangle',205,82,.075,.20,.002);                         // launcher body kick
 sfxBurst(t+.012,.105,'lowpass',1250,180,.8,.38,.002,true);           // compressed-air piston thump
 sfxBurst(t+.018,.15,'bandpass',760,2300,1.35,.24,.006);              // pressurised mechanism release
 sfxTone(t+.025,'sawtooth',145,610,.19,.10,.008);                     // small electric / spring motor winding up
 sfxBurst(t+.055,.27,'bandpass',5200,1250,1.1,.22,.012);              // steel cable rapidly paying out
 sfxBurst(t+.075,.22,'highpass',6400,1900,1.4,.11,.008);              // cable hiss and air shear
 for(let i=0;i<5;i++)sfxBurst(t+.09+i*.027,.018,'bandpass',2450-i*155,1500,5,.075,.001); // spool teeth
 sfxTone(t+.27,'sine',1550,920,.11,.045,.004);                        // cable end ringing as it leaves the launcher
}
function sfxHookAttach(){
 const t=SFX.ctx.currentTime+.003;
 // A hard point strikes the surface, the claw bites, then the cable takes tension.
 sfxBurst(t,.052,'lowpass',2100,150,.85,.48,.001,true);               // damped impact into the target
 sfxTone(t,'triangle',172,48,.19,.46,.002);                            // deep hook bite / body resonance
 sfxBurst(t+.006,.075,'bandpass',1750,520,.95,.28,.001);               // metal tip scraping and seating
 sfxBurst(t+.018,.052,'highpass',5200,2500,1.8,.14,.001);              // sharp metal catch
 sfxTone(t+.035,'sine',1180,760,.12,.075,.003);                        // brief metal ring
 sfxTone(t+.045,'triangle',285,105,.22,.22,.004);                      // cable pulls taut
 sfxBurst(t+.05,.20,'bandpass',980,230,1.1,.17,.012,true);             // short tension shudder through the cable
}
function sfxHookRelease(){
 const t=SFX.ctx.currentTime+.003;
 sfxBurst(t,.18,'bandpass',3200,900,1.6,.3,.01);                            // slack line whips back
 for(let i=0;i<6;i++)sfxBurst(t+.02+i*(.03-i*.003),.012,'bandpass',2400-i*120,2200,6,.07*(1-i*.1),.001);   // spool ratchet
 sfxBurst(t+.12,.15,'lowpass',1400,200,.6,.2,.005,true);                     // rope falling loose
 sfxTone(t,'sine',500,200,.06,.05,.004);
}
function sfxChargeStart(){const t=SFX.ctx.currentTime+.003;sfxBurst(t,.28,'bandpass',500,1700,1.2,.1,.08,true);sfxTone(t,'sine',90,160,.25,.12,.03);}   // blade drawn back, breath in
function sfxChargeReady(){   // fully charged: bright power chord + shimmer + sub boom
 const t=SFX.ctx.currentTime+.003;
 [330,495,660,990].forEach((f,i)=>sfxTone(t+i*.012,'triangle',f,f*1.012,1.1,.07,.02));
 sfxTone(t,'sine',82,58,.65,.38,.004);
 sfxBurst(t,.75,'bandpass',1500,7000,2.4,.15,.1);
 [3100,4650].forEach(f=>sfxTone(t+.02,'sine',f,f*.998,.9,.045,.003));
}
function sfxLungeBurst(){   // the charged strike is released: battle cry, blade whoosh, boom, steel ring
 const t=SFX.ctx.currentTime+.003;
 sfxVoice(t+.005,{f0:340,f1:245,dur:.46,gain:.4,vowel:'a',breath:.22,att:.015});
 sfxBurst(t,.5,'bandpass',350,4200,1.1,.6,.05);
 sfxBurst(t,.38,'lowpass',2500,200,.6,.45,.01,true);
 sfxTone(t,'sine',140,38,.55,.55,.004);
 [3200,4800,6400].forEach((f,i)=>sfxTone(t+.03,'sine',f,f*.997,.8-i*.15,.05,.002));
}
// returns true when the new engine handled the sound type (the old synth is skipped)
function sfxPlay(type){
 if(type!=='jump'&&type!=='land'&&type!=='hook'&&type!=='attach'&&type!=='release'&&type!=='block'&&type!=='levelup'&&type!=='upgrade'&&type!=='monsterHurt')return false;
 try{
  if(!sfxReady())return true;
  const ac=SFX.ctx,now=ac.currentTime;if(SFX.last[type]&&now-SFX.last[type]<.06)return true;SFX.last[type]=now;
  if(type==='jump')sfxJump();else if(type==='land')sfxLand(16);else if(type==='hook')sfxHookFire();else if(type==='attach')sfxHookAttach();else if(type==='block')sfxBlock();else if(type==='levelup')sfxLevelUp();else if(type==='upgrade')sfxUpgrade();else if(type==='monsterHurt')sfxMonsterHurt();else sfxHookRelease();
  return true;
 }catch(e){return false;}
}
// ---- continuous sounds: wind, cable tension, charge ----
function sfxLoops(){
 if(SFX.wind)return;const ac=SFX.ctx;
 const ns=(buf)=>{const s=ac.createBufferSource();s.buffer=buf;s.loop=true;s.start(0,Math.random());return s;};
 const flt=(type,f,q)=>{const b=ac.createBiquadFilter();b.type=type;b.frequency.value=f;b.Q.value=q;return b;};
 const gn=()=>{const g=ac.createGain();g.gain.value=0;return g;};
 const W={};   // wind: soft body + whistling + low rumble
 W.lp=flt('lowpass',400,.7);W.g=gn();ns(SFX.pink).connect(W.lp);W.lp.connect(W.g);W.g.connect(SFX.out);
 W.bp=flt('bandpass',1200,6);W.g2=gn();ns(SFX.white).connect(W.bp);W.bp.connect(W.g2);W.g2.connect(SFX.out);
 W.rl=flt('lowpass',140,.8);W.g3=gn();ns(SFX.pink).connect(W.rl);W.rl.connect(W.g3);W.g3.connect(SFX.out);
 SFX.wind=W;
 const R={};   // cable under load: stick-slip creak + fibre friction
 R.o=ac.createOscillator();R.o.type='sawtooth';R.o.frequency.value=60;R.bp=flt('bandpass',520,4);R.g=gn();R.o.connect(R.bp);R.bp.connect(R.g);R.g.connect(SFX.out);R.o.start();
 R.bp2=flt('bandpass',2200,3);R.g2=gn();ns(SFX.white).connect(R.bp2);R.bp2.connect(R.g2);R.g2.connect(SFX.out);
 SFX.rope=R;
 const C={};   // charge: rising detuned saws + fifth + octave sine, tremolo that speeds up, shimmering noise
 C.lp=flt('lowpass',300,1.2);C.trem=ac.createGain();C.trem.gain.value=.65;C.g=gn();
 C.oa=ac.createOscillator();C.oa.type='sawtooth';C.ob=ac.createOscillator();C.ob.type='sawtooth';C.oc=ac.createOscillator();C.oc.type='sine';C.od=ac.createOscillator();C.od.type='sawtooth';
 const mix=ac.createGain();mix.gain.value=.5;
 [[C.oa,1],[C.ob,.8],[C.oc,.7],[C.od,.4]].forEach(([o,v])=>{const g=ac.createGain();g.gain.value=v;o.frequency.value=110;o.connect(g);g.connect(mix);o.start();});
 mix.connect(C.lp);C.lp.connect(C.trem);C.trem.connect(C.g);C.g.connect(SFX.out);
 C.lfo=ac.createOscillator();C.lfo.frequency.value=6;C.ld=ac.createGain();C.ld.gain.value=.3;C.lfo.connect(C.ld);C.ld.connect(C.trem.gain);C.lfo.start();
 C.sb=flt('bandpass',900,3.5);C.sg=gn();ns(SFX.white).connect(C.sb);C.sb.connect(C.sg);C.sg.connect(SFX.out);
 SFX.chg=C;
}
function sfxUpdate(dt){
 if(!SFX.ctx){if(!running||!sfxReady())return;}
 const ac=SFX.ctx;if(!SFX.out)return;sfxLoops();
 const now=ac.currentTime,live=running&&mouse.locked&&!playerDeath.active;
 SFX.out.gain.setTargetAtTime(sfxVol(),now,.05);
 // --- wind: louder and brighter the faster the player drops (a little extra when flying fast on the cable) ---
 const W=SFX.wind;let ws=0;
 if(live&&!player.grounded&&!player.climbing&&!player.onWall){const vy=Math.max(0,-player.vel.y),hs=Math.hypot(player.vel.x,player.vel.z);ws=vy+Math.max(0,hs-14)*.35;}
 const w=sfxSm(6,46,ws),gust=1+.1*Math.sin(now*9)+.07*Math.sin(now*23.7),tc=w>.001?.07:.2;
 W.g.gain.setTargetAtTime(.62*Math.pow(w,1.1)*gust,now,tc);
 W.lp.frequency.setTargetAtTime(320+3000*w,now,.08);
 W.g2.gain.setTargetAtTime(.1*w*w*gust,now,tc);W.bp.frequency.setTargetAtTime(800+1700*w,now,.08);
 W.g3.gain.setTargetAtTime(.45*w,now,tc);
 // --- cable under tension ---
 const R=SFX.rope;let ten=0;
 if(live){
  const sp=Math.hypot(player.vel.x,player.vel.y,player.vel.z);
  if(grapplePull&&grapplePull.active)ten=sfxCl(.45+sp/90,0,1);
  else for(const h of hooks){if(h.mode==='attached'&&h.anchor){const ex=h.anchor.distanceTo(getHandWorld(h.side))-h.length;ten=Math.max(ten,sfxCl(.12+Math.max(0,ex)*.18+sp/70,0,1));}}
 }
 const stutter=Math.random()<.22?.3:1;
 R.g.gain.setTargetAtTime(.24*Math.pow(ten,1.3)*stutter,now,.03);
 R.o.frequency.setTargetAtTime(42+ten*85+(Math.random()-.5)*26,now,.02);
 R.bp.frequency.setTargetAtTime(380+ten*700+(Math.random()-.5)*160,now,.03);
 R.g2.gain.setTargetAtTime(.11*ten*ten,now,.06);R.bp2.frequency.setTargetAtTime(1600+ten*1500,now,.06);
 // --- charged sword strike ---
 const C=SFX.chg,chgOn=live&&CHG.down&&CHG.t>LUNGE.delay&&!player.lunge;
 if(chgOn){
  const p=sfxCl((CHG.t-LUNGE.delay)/(LUNGE.charge-LUNGE.delay),0,1),rdy=CHG.ready?1:0;
  if(!SFX.pChg)sfxChargeStart();
  const f=110*Math.pow(3,p)*(1+.05*rdy);
  C.oa.frequency.setTargetAtTime(f,now,.04);C.ob.frequency.setTargetAtTime(f*1.007,now,.04);C.oc.frequency.setTargetAtTime(f*2,now,.04);C.od.frequency.setTargetAtTime(f*1.5,now,.04);
  C.lp.frequency.setTargetAtTime(260+4800*p*p+1200*rdy,now,.05);
  C.lfo.frequency.setTargetAtTime(6+14*p+6*rdy,now,.05);
  C.g.gain.setTargetAtTime(.12+.3*p+.12*rdy,now,.05);
  C.sb.frequency.setTargetAtTime(700+5200*p,now,.05);C.sg.gain.setTargetAtTime(.02+.12*p*p+.05*rdy,now,.05);
  if(CHG.ready&&!SFX.pReady)sfxChargeReady();
  SFX.pReady=!!CHG.ready;
 }else{
  C.g.gain.setTargetAtTime(0,now,.04);C.sg.gain.setTargetAtTime(0,now,.04);SFX.pReady=false;
 }
 SFX.pChg=chgOn;
 const lg=!!player.lunge;if(lg&&!SFX.pLunge&&live)sfxLungeBurst();SFX.pLunge=lg;
 // --- captive under attack: warning right away, then repeated every 5 s while monsters keep hitting her ---
 if(live){if(SFX.capT>0)SFX.capT-=dt;if(CAPTIVE.alive&&CAPTIVE.under>0&&SFX.capT<=0){sfxCaptiveAlarm();SFX.capT=5;}}
}
function sound(type){
 try{
  if(sfxPlay(type))return;
  if(type==='step'){playAsset('run',true);return;}
  if(type==='bow'){playAssetNow('bow');return;}
  if(type==='monster'){playAssetNow('monster');return;}
  if(type==='monsterDie'){playAssetNow('monsterDie');return;}
  if(type==='swordGround'){playAssetNow('swordGround');return;}
  if(type==='swordHit'){playAssetNow('swordHit');return;}
  if(audioSettings.muted||audioSettings.master*audioSettings.effects<=0)return;
  if(!audioCtx)audioCtx=new (window.AudioContext||window.webkitAudioContext)();
  if(audioCtx.state==='suspended')audioCtx.resume();
  const now=audioCtx.currentTime,osc=audioCtx.createOscillator(),gain=audioCtx.createGain();
  osc.connect(gain);gain.connect(audioCtx.destination);
  const preset={hook:[480,120,.11,'sawtooth'],attach:[750,280,.09,'triangle'],release:[240,90,.1,'triangle'],jump:[180,80,.08,'sine'],land:[90,40,.13,'triangle'],slide:[110,60,.13,'sawtooth'],arrowhit:[170,55,.08,'square'],draw:[130,200,.05,'sine']}[type]||[220,120,.07,'sine'];
  osc.type=preset[3];osc.frequency.setValueAtTime(preset[0],now);osc.frequency.exponentialRampToValueAtTime(Math.max(30,preset[1]),now+preset[2]);
  gain.gain.setValueAtTime(.0001,now);gain.gain.exponentialRampToValueAtTime(.07*audioSettings.master*audioSettings.effects,now+.008);gain.gain.exponentialRampToValueAtTime(.0001,now+preset[2]);
  osc.start(now);osc.stop(now+preset[2]+.02);
 }catch(e){}
}
function startRun(){startGameplayMusic();try{sfxReady();}catch(e){}ui.main.classList.add('hidden');ui.controls.classList.add('hidden');ui.pause.classList.add('hidden');ui.loading.classList.add('hidden');if(!started){resetPlayer();started=true;}running=true;paused=false;renderer.domElement.requestPointerLock?.();showToast('Find a rooftop. Build momentum.');}
function resetPlayer(){try{playerDeathReset();}catch(e){}try{superReset();}catch(e){}try{lungeReset();}catch(e){}try{upgReset();}catch(e){}try{stamReset();}catch(e){}try{XPSYS.level=1;XPSYS.cur=0;XPSYS.dry=0;XPSYS.pulse=0;XPSYS.shown='';}catch(e){}player.dash=null;DASH.cool=0;stopAim();player.fallRoll=null;player.slam=null;player.kick=null;try{captiveReset();}catch(e){}grapplePull=null;player.pos.set(4,0,3);player.vel.set(0,0,0);player.yaw=0;player.pitch=0;player.grounded=false;player.onWall=false;player.climbing=false;player.mantle=null;player.postFlight=false;player.wallTime=0;player.sliding=false;player.slideTime=0;player.eye=1.65;player.state='IDLE';player.airTime=0;player.landTime=0;viewBob=0;viewRoll=0;for(const h of hooks)detachHook(h,false);resetErikaAnimation();playerHealth=UP.maxHp;playerHurtCooldown=0;monsterRespawnTimer=0;if(monsterHurtFlash)monsterHurtFlash.style.opacity='0';resetMonsters();syncPlayerVisuals();}
function enterPause(){if(!started)return;startMenuMusic();running=false;paused=true;stopRunFootsteps();ui.pause.classList.remove('hidden');if(document.pointerLockElement)document.exitPointerLock();ui.hint.textContent='';}
function resumeRun(){startGameplayMusic();ui.pause.classList.add('hidden');running=true;paused=false;renderer.domElement.requestPointerLock?.();}
function goMainMenu(){startMenuMusic();running=false;paused=false;stopRunFootsteps();ui.pause.classList.add('hidden');ui.main.classList.remove('hidden');if(document.pointerLockElement)document.exitPointerLock();detachAll(false);}
function syncPlayerVisuals(dt=1/60){
 if(!playerMesh||!camera)return;
 playerMesh.position.copy(player.pos);playerMesh.position.y-=superCrouchDrop();{let yy=player.yaw+(erikaAnim.ready&&thirdPerson?erikaAnim.heading+(erikaAnim.aimYawOff||0):0);const KK=player.kick;if(KK&&KK.w>.01&&thirdPerson)yy+=mnWrap(KK.theta-yy)*Math.min(1,KK.w*1.6);playerMesh.rotation.y=yy;superBodyApply(yy);lungeSafe(lungeLeanApply);}playerMesh.updateMatrixWorld(true);
 camera.rotation.order='YXZ';
 if(!thirdPerson){
  // While climbing, the camera rides the head of the climb animation (step bob + sway), then eases back out.
  const hb=erikaPlayer&&erikaPlayer.bones&&erikaPlayer.bones.head;
  if(player.climbing&&hb&&erikaAnim.ready){
   hb.getWorldPosition(climbCam.tmp).sub(player.pos);
   if(!climbCam.on){climbCam.mean.copy(climbCam.tmp);climbCam.on=true;}
   climbCam.mean.lerp(climbCam.tmp,1-Math.exp(-1.4*dt));
   climbCam.tmp.sub(climbCam.mean).multiplyScalar(.85).clampLength(0,.22);
  }else{climbCam.on=false;climbCam.tmp.set(0,0,0);}
  climbCam.d.lerp(climbCam.tmp,1-Math.exp(-16*dt));
  camera.position.set(player.pos.x+climbCam.d.x,player.pos.y+player.eye+viewBob+climbCam.d.y,player.pos.z+climbCam.d.z);
  camera.rotation.y=player.yaw;camera.rotation.x=player.pitch;camera.rotation.z=viewRoll+(player.climbing?climbCam.d.x*0:0);
  cameraPositionInitialized=false;
  return;
 }
 // Shoulder camera: stays behind the ninja even when aiming up/down, and avoids looking through the character's head.
 const right=new THREE.Vector3(Math.cos(player.yaw),0,-Math.sin(player.yaw)).normalize();
 const focus=new THREE.Vector3(player.pos.x,player.pos.y+(player.sliding?.98:1.18),player.pos.z);
 if(playerDeath.active){const dk=erikaSmoothstep(0,1.6,playerDeath.t),yy=playerMesh.rotation.y;focus.y-=.55*dk;focus.x+=Math.sin(yy)*.45*dk;focus.z+=Math.cos(yy)*.45*dk;}   // follow the body as it falls backwards
 let cameraSupportTargetY=.25;for(const c of colliders){if(!insideXZ(c,player.pos.x,player.pos.z,.2)||c.top>player.pos.y+.08)continue;cameraSupportTargetY=Math.max(cameraSupportTargetY,c.top+.25);}const roofFloor=roofSurfaceAt(player.pos.x,player.pos.z);if(roofFloor!==null&&roofFloor<=player.pos.y+.08)cameraSupportTargetY=Math.max(cameraSupportTargetY,roofFloor+.25);if(!cameraPositionInitialized||!(dt>0)||!Number.isFinite(dt))cameraSupportFollowY=cameraSupportTargetY;else cameraSupportFollowY=THREE.MathUtils.damp(cameraSupportFollowY,cameraSupportTargetY,8,dt);const cameraFloorY=Math.max(.25,cameraSupportFollowY),cameraClearance=Math.max(.05,focus.y-cameraFloorY);
 let cameraPitch=player.pitch;cameraPitch=Math.min(cameraPitch,Math.atan(cameraClearance/.85));
 const cp=Math.cos(cameraPitch),forward=new THREE.Vector3(-Math.sin(player.yaw)*cp,Math.sin(cameraPitch),-Math.cos(player.yaw)*cp).normalize();
 let boomDistance=THIRD_PERSON_DISTANCE*(1-.34*bow.aimW);if(forward.y>.001)boomDistance=Math.min(boomDistance,cameraClearance/forward.y);
 const shoulderOffset=(.2+.1*bow.aimW)*Math.max(.12,Math.cos(cameraPitch)**2);
 let desired=focus.clone().addScaledVector(forward,-boomDistance).addScaledVector(right,shoulderOffset);
 // Pull the camera closer if a building or the circular wall blocks the boom.
 const rayVec=desired.clone().sub(focus),rayLength=rayVec.length();
 if(rayLength>.05&&raycaster&&solidMeshes.length){
  rayVec.normalize();raycaster.set(focus,rayVec);raycaster.near=.15;raycaster.far=rayLength;
  const hits=raycaster.intersectObjects(solidMeshes,false);
  if(hits.length){const safeDistance=Math.max(.8,hits[0].distance-.35);desired.copy(focus).addScaledVector(rayVec,safeDistance);}
 }
 if(!cameraPositionInitialized||!(dt>0)||!Number.isFinite(dt)){camera.position.copy(desired);cameraPositionInitialized=true;}
 else{const cameraSpeed=player.vel.length(),followRate=THREE.MathUtils.clamp(34+cameraSpeed*.3,34,60);camera.position.lerp(desired,1-Math.exp(-followRate*dt));}
 const aimDir=focus.clone().sub(camera.position).normalize(),cameraUp=new THREE.Vector3(0,1,0).addScaledVector(aimDir,-aimDir.y).normalize(),aimTarget=focus.clone().addScaledVector(aimDir,20).addScaledVector(cameraUp,4.5);
 camera.lookAt(aimTarget);camera.rotation.z=viewRoll*.45;
}
function raycastTarget(origin,direction,maxDistance=500){raycaster.set(origin,direction.clone().normalize());raycaster.near=0.05;raycaster.far=maxDistance;const hits=raycaster.intersectObjects(grappleTargetMeshes,false);for(const hit of hits){if(hit.distance<0.12)continue;return hit;}return null;}
function worldHitNormal(hit){const n=hit.face?hit.face.normal.clone():v3(0,1,0);if(hit.object){hit.object.updateMatrixWorld(true);n.applyMatrix3(new THREE.Matrix3().getNormalMatrix(hit.object.matrixWorld)).normalize();}return n;}
// ===================== CABLE KICK: F on a monster -> both cables hit it, the player flies in and kicks it down =====================
// Tweak: KICK.damage / KICK.fall / KICK.lie / KICK.rise (seconds the monster spends falling, lying, getting up)
const KICK={damage:100,fall:.3,lie:1,rise:.4};
const _kk={f:new THREE.Vector3(),r:new THREE.Vector3(),UP:new THREE.Vector3(0,1,0),h:new THREE.Vector3(),c:new THREE.Vector3(),tgt:new THREE.Vector3(),hint:new THREE.Vector3(),to:new THREE.Vector3(),tc:new THREE.Vector3(),A:new THREE.Vector3(),B:new THREE.Vector3(),C:new THREE.Vector3(),dir:new THREE.Vector3(),p:new THREE.Vector3(),Bn:new THREE.Vector3(),v1:new THREE.Vector3(),v2:new THREE.Vector3()};
function pickKickTarget(){
 if(!camera)return null;const o=camera.position,dir=cameraDir().clone().normalize();let best=null,bs=-1,bd=0;
 for(const m of monsters){if(!m.alive||m.entry||!m.root.visible)continue;const p=m.root.position,sc=m.cfg.scale;
  const tx=p.x-o.x,ty=p.y+1.2*sc-o.y,tz=p.z-o.z,d=Math.hypot(tx,ty,tz);if(d>ROPE_MAX||d<2)continue;
  const dot=(tx*dir.x+ty*dir.y+tz*dir.z)/d,need=Math.cos(Math.atan2(sc*.9,d)+.09);   // inside the monster's apparent size plus ~5 degrees of aim assist
  if(dot>need&&dot>bs){bs=dot;best=m;bd=d;}}
 if(best){const p=best.root.position,to=new THREE.Vector3(p.x-o.x,p.y+1.2*best.cfg.scale-o.y,p.z-o.z).normalize();const hit=raycastTarget(o.clone(),to,bd);if(hit&&hit.distance<bd-1.5)return null;}   // a wall is in the way
 return best;
}
function startMonsterKick(m){
 if(player.slam||player.kick)return;detachAll(false);player.postFlight=false;player.sliding=false;
 const p=m.root.position,pos=new THREE.Vector3(p.x,p.y+1.2*m.cfg.scale,p.z);
 grapplePull={active:false,target:pos.clone(),anchor:pos.clone(),startedAt:elapsed};
 for(const h of hooks){const start=getHandWorld(h.side);h.held=true;h.autoPull=true;h.mode='flying';h.projectile={start,target:pos.clone(),normal:new THREE.Vector3(0,1,0),distance:start.distanceTo(pos),elapsed:0,object:null,autoPull:true};h.anchor=null;h.length=0;h.tip.visible=true;h.mesh.visible=true;h.tip.position.copy(start);h.mesh.position.copy(start);}
 player.kick={m,phase:'fly',t:0,w:0,theta:player.yaw};sound('hook');showToast('CABLE KICK!');
}
function endKick(){detachAll(false);player.kick=null;}
function startMonsterDown(m){m.down={t:0,init:false};if(m.anim)m.anim.attackT=-1;}
function monsterDownStep(m,dt){
 const d=m.down,A=m.anim;if(!d.air)mnSettleY(m,dt);
 if(!d.init){d.init=true;A.attackT=-1;mnCopy(A.deathFrom,A.pose);A.deathType='back';for(let i=0;i<2;i++){const s=i?1:-1;A.rel[i][0]=s*(m.hipW+.075);A.rel[i][1]=-.89*m.legReach;A.rel[i][2]=-.04;}}
 if(d.air){   // thrown up by the leap strike: ballistic flight, body tilting back
  d.at=(d.at||0)+dt;d.vy-=JSTRIKE.grav*dt;const mp=m.root.position;mp.y+=d.vy*dt;
  if(mp.y<=m.spawn.y&&d.vy<0){mp.y=m.spawn.y;d.air=false;d.t=0;d.tt0=d.tt||0;slamFx.shake=Math.max(slamFx.shake||0,.18);}
  else{d.tt=.45*Math.min(1,d.at/.45);mnDeathPose(m,d.tt,A.tmp);mnApplyPose(m,A.tmp);return;}
 }
 const fl=d.fall||KICK.fall,li=d.lie||KICK.lie,f0=d.tt0||0;
 d.t+=dt;const t=d.t,tt=t<fl?f0+(.85-f0)*(t/fl):t<fl+li?.85:.85*Math.max(0,1-(t-fl-li)/KICK.rise);   // fall, lie sprawled on the ground, get back up
 d.cur=tt;mnDeathPose(m,tt,A.tmp);mnApplyPose(m,A.tmp);
 if(t>=fl+li+KICK.rise){m.down=null;for(let i=0;i<2;i++){A.rel[i][0]=A.rel[i][1]=A.rel[i][2]=0;}A.stun=.15;A.lastX=m.root.position.x;A.lastZ=m.root.position.z;m.attackCooldown=Math.max(m.attackCooldown,.5);}
}
function kickUpdate(dt){
 const k=player.kick;if(!k)return;const m=k.m;k.t+=dt;
 if(k.phase==='fly'){
  if(!m.alive||m.entry||k.t>3.5){endKick();return;}
  k.w=Math.min(1,k.w+dt/.18);
  const mp=m.root.position,sc=m.cfg.scale,cx=mp.x,cy=mp.y+1.2*sc,cz=mp.z;
  const dx=player.pos.x-cx,dz=player.pos.z-cz,dy=player.pos.y+1-cy,d=Math.hypot(dx,dy,dz)||1,reach=MONSTER_BODY*sc+1.3,near=d<reach+1.6;
  if(!grapplePull&&k.t>.1&&!near){endKick();return;}
  if(grapplePull){grapplePull.target.set(cx+dx/d*(reach-1.5),cy+dy/d*(reach-1.5)-1,cz+dz/d*(reach-1.5));grapplePull.anchor.set(cx,cy,cz);}
  for(const h of hooks)if(h.mode==='attached'&&h.anchor)h.anchor.set(cx,cy,cz);   // the cables stay stuck to the moving monster
  k.theta=Math.atan2(cx-player.pos.x,cz-player.pos.z)+Math.PI;
  if((grapplePull&&grapplePull.active&&d<reach+.25)||(!grapplePull&&near&&k.t>.05)){   // also strikes if the normal pull released right at the monster
   k.phase='strike';k.t=0;damageMonster(m,KICK.damage,'kick');
   if(m.alive&&!m.boss){startMonsterDown(m);try{mnKnock(m,3/sc);}catch(e){}}
   swordHitFx(m,2);slamFx.shake=Math.max(slamFx.shake||0,.5);try{sound('land');}catch(e){}
   detachAll(false);player.vel.set(-dx/d*7,5.5,-dz/d*7);player.grounded=false;
  }
 }else if(k.phase==='strike'){if(k.t>.28){k.phase='recover';k.t=0;}}
 else{k.w-=dt/.3;if(k.w<=0)player.kick=null;}
}
// Flying-kick pose, applied after the animation mixer: body leans back, right leg thrust at the monster, left leg tucked, arms out.
function kickLegIK(up,kn,ft,target,hint,w){
 const K=_kk;
 for(let pass=0;pass<2;pass++){
  up.getWorldPosition(K.A);kn.getWorldPosition(K.B);ft.getWorldPosition(K.C);
  const L1=K.A.distanceTo(K.B),L2=K.B.distanceTo(K.C);if(L1<1e-4||L2<1e-4)return;
  K.dir.copy(target).sub(K.A);let dist=K.dir.length();if(dist<1e-4)return;K.dir.divideScalar(dist);
  dist=THREE.MathUtils.clamp(dist,Math.abs(L1-L2)+.02,(L1+L2)*.998);
  K.p.copy(hint).addScaledVector(K.dir,-hint.dot(K.dir));if(K.p.lengthSq()<1e-6)K.p.set(0,1,0);K.p.normalize();
  const cosA=THREE.MathUtils.clamp((L1*L1+dist*dist-L2*L2)/(2*L1*dist),-1,1),sinA=Math.sqrt(1-cosA*cosA);
  K.Bn.copy(K.A).addScaledVector(K.dir,L1*cosA).addScaledVector(K.p,L1*sinA);
  K.v1.copy(K.B).sub(K.A).normalize();K.v2.copy(K.Bn).sub(K.A).normalize();_ikTurnBone(up,K.v1,K.v2,w);
  kn.getWorldPosition(K.B);ft.getWorldPosition(K.C);K.v1.copy(K.C).sub(K.B).normalize();K.v2.copy(target).sub(K.B).normalize();_ikTurnBone(kn,K.v1,K.v2,w);
 }
}
function kickPoseIK(){
 const k=player.kick;if(!k||!(k.w>.01)||!erikaPlayer||!erikaPlayer.bones||!playerMesh)return;
 const bn=erikaPlayer.bones,K=_kk,w=Math.min(1,k.w),m=k.m;
 if(!bn.hips||!bn.rightUpLeg||!bn.rightLeg||!bn.rightFoot||!bn.leftUpLeg||!bn.leftLeg||!bn.leftFoot)return;
 const mp=m.root.position;K.tc.set(mp.x,mp.y+1.2*m.cfg.scale,mp.z);
 const rec=k.hipRec||(k.hipRec={pre:new THREE.Quaternion(),post:new THREE.Quaternion(),has:false});
 if(rec.has&&bn.hips.quaternion.angleTo(rec.post)<1e-5)bn.hips.quaternion.copy(rec.pre);   // animation did not rewrite the hips this frame: undo our last tilt instead of stacking another
 rec.pre.copy(bn.hips.quaternion);
 playerMesh.updateMatrixWorld(true);bn.hips.getWorldPosition(K.h);
 K.f.copy(K.tc).sub(K.h);K.f.y=0;if(K.f.lengthSq()<1e-6)K.f.set(0,0,-1);K.f.normalize();K.r.crossVectors(K.f,K.UP);
 const th=.95*w;K.to.copy(K.UP).multiplyScalar(Math.cos(th)).addScaledVector(K.f,-Math.sin(th));
 _ikTurnBone(bn.hips,K.UP,K.to,1);   // lean back: head back, legs forward
 rec.post.copy(bn.hips.quaternion);rec.has=true;
 playerMesh.updateMatrixWorld(true);bn.hips.getWorldPosition(K.h);
 bn.rightUpLeg.getWorldPosition(K.A);bn.rightLeg.getWorldPosition(K.B);bn.rightFoot.getWorldPosition(K.C);
 const legLen=K.A.distanceTo(K.B)+K.B.distanceTo(K.C);
 K.dir.copy(K.tc).sub(K.h).normalize();K.tgt.copy(K.h).addScaledVector(K.dir,legLen*.98);
 kickLegIK(bn.rightUpLeg,bn.rightLeg,bn.rightFoot,K.tgt,K.UP,w);
 K.tgt.copy(K.h).addScaledVector(K.f,.28).addScaledVector(K.UP,-.55).addScaledVector(K.r,-.12);
 kickLegIK(bn.leftUpLeg,bn.leftLeg,bn.leftFoot,K.tgt,K.f,w);
 const chest=bn.spine2||bn.spine1||bn.spine||bn.hips;chest.getWorldPosition(K.c);
 K.tgt.copy(K.c).addScaledVector(K.r,.8).addScaledVector(K.UP,.1);K.hint.copy(K.r).addScaledVector(K.UP,-.5);slamArmIK(1,K.tgt,K.hint,w*.8);
 K.tgt.copy(K.c).addScaledVector(K.r,-.8).addScaledVector(K.UP,.15);K.hint.copy(K.r).multiplyScalar(-1).addScaledVector(K.UP,-.5);slamArmIK(-1,K.tgt,K.hint,w*.8);
}
function fireBothHooks(){if(!running)return;if(grapplePull||hooks.some(h=>h.mode!=='ready')){detachAll(true);showToast('DUAL HOOKS RELEASED');return;}const km=pickKickTarget();if(km){startMonsterKick(km);return;}const hit=raycastTarget(camera.position.clone(),cameraDir(),ROPE_MAX);if(!hit){showToast('Out of rope range ('+ROPE_MAX+' m)');sound('release');return;}detachAll(false);const normal=worldHitNormal(hit);const target=hit.point.clone();if(normal.y>.58){target.addScaledVector(normal,.45);target.y=Math.max(hit.point.y+.18,target.y);}else{target.addScaledVector(normal,2.5);target.y-=1.2;}const radial=Math.hypot(target.x,target.z),limit=WORLD.wallRadius-7;if(radial>limit){target.x*=limit/radial;target.z*=limit/radial;}grapplePull={active:false,target,anchor:hit.point.clone(),startedAt:elapsed};for(const h of hooks){const start=getHandWorld(h.side);h.held=true;h.autoPull=true;h.mode='flying';h.projectile={start,target:hit.point.clone(),normal:normal.clone(),distance:start.distanceTo(hit.point),elapsed:0,object:hit.object,autoPull:true};h.anchor=null;h.length=0;h.tip.visible=true;h.mesh.visible=true;h.tip.position.copy(start);h.mesh.position.copy(start);}sound('hook');showToast('DUAL HOOKS FIRED');}
function attachHook(h){if(!h.projectile)return;const isAuto=!!h.projectile.autoPull;h.anchor=h.projectile.target.clone();h.projectile=null;h.mode='attached';const origin=getHandWorld(h.side);const d=origin.distanceTo(h.anchor);h.length=Math.max(4,d-Math.max(5,d*.28));h.tip.visible=true;h.mesh.visible=true;h.tip.position.copy(h.anchor);h.mesh.position.copy(h.anchor);if(isAuto&&grapplePull)grapplePull.active=true;sound('attach');showToast(isAuto?'DUAL PULL ENGAGED':`${h.name} CABLE ATTACHED`);}
function detachHook(h,playSound=true){if(h.mode!=='ready'&&playSound)sound('release');h.held=false;h.mode='ready';h.anchor=null;h.projectile=null;h.length=0;h.autoPull=false;if(h.line){h.line.visible=false;}if(h.tip)h.tip.visible=false;if(h.mesh)h.mesh.visible=false;}
function detachAll(playSound=true){for(const h of hooks)detachHook(h,playSound);grapplePull=null;}
function updateHooks(dt){updateHipLaunchers();let attached=0;for(const h of hooks){const hand=getHandWorld(h.side);if(h.mode==='flying'&&h.projectile){h.projectile.elapsed+=dt;const dur=Math.max(.045,h.projectile.distance/240);const t=Math.min(1,h.projectile.elapsed/dur);const pos=hand.clone().lerp(h.projectile.target,t);h.tip.visible=true;h.mesh.visible=true;h.tip.position.copy(pos);h.mesh.position.copy(pos);if(t>=1)attachHook(h);}
 if(h.mode==='attached'&&h.anchor){attached++;const distance=hand.distanceTo(h.anchor);if(distance>ROPE_MAX+12||!Number.isFinite(distance)){detachHook(h,false);if(grapplePull&&!hooks.some(o=>o.mode!=='ready'))grapplePull=null;showToast('CABLE SNAPPED - TOO LONG');continue;}h.tip.position.copy(h.anchor);h.mesh.position.copy(h.anchor);const dir=hand.clone().sub(h.anchor).normalize();h.mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),dir);}
 if(h.mode==='attached'||h.mode==='flying'){h.line.visible=true;const end=h.mode==='attached'?h.anchor:(h.tip.position);setCableSegment(h.line,hand,end);}else if(h.line)h.line.visible=false;
 }
 updateHookUI();return attached;}
function updateHookUI(){for(const [i,h] of hooks.entries()){const box=$(i===0?'leftHookBox':'rightHookBox'),state=$(i===0?'leftState':'rightState');box.classList.toggle('active',h.mode!=='ready');state.textContent=h.mode==='attached'?'LOCKED':h.mode==='flying'?'FIRING':h.held?'READY':'READY';}}
function moveInput(){if(rollLocked())return v3();const dir=v3();const forward=new THREE.Vector3(-Math.sin(player.yaw),0,-Math.cos(player.yaw));const right=new THREE.Vector3(Math.cos(player.yaw),0,-Math.sin(player.yaw));if(keys.KeyW)dir.add(forward);if(keys.KeyS)dir.sub(forward);if(keys.KeyD)dir.add(right);if(keys.KeyA)dir.sub(right);if(dir.lengthSq()>0)dir.normalize();return dir;}
// The triangular gable end above a building's front/back wall is part of that wall: climbing it ends on the roof (ridge / slope), not at the wall top.
const GWALL={map:null};
function gableWallFor(c,px){
 if(!GWALL.map){GWALL.map=new Map();for(const g of colliders){if(g.kind==='gable'&&Math.abs(g.top-g.bottom-.45)<.01)GWALL.map.set(g.x+'|'+g.z,{halfX:g.halfX,v:null});}}
 const g=GWALL.map.get(c.x+'|'+c.z);if(!g||Math.abs(px-c.x)>g.halfX-.05)return null;
 const t=roofSurfaceAt(px,c.z);if(t===null)return null;
 if(!g.v)g.v={x:c.x,z:c.z,halfX:g.halfX,halfZ:c.halfZ,top:t,kind:'gablewall',virtual:true};
 g.v.top=t;return g.v;
}
function nearWall(){let best=null,bestDist=1.2,bestNP=null,bestNPd=1.8;const px=player.pos.x,pz=player.pos.z;
 for(const c0 of colliders){if(c0.kind==='roof'||c0.kind==='gable'||c0.kind==='post'||c0.noClimb)continue;let c=c0;
  if(c0.kind==='building'&&(player.climbing||player.pos.y+.5>=c0.top)){const gv=gableWallFor(c0,px);if(gv)c=gv;}   // in front of / behind the triangle: the wall continues up to the roof surface
  const yOk=player.pos.y+.5<c.top&&player.pos.y+2>0;if(!yOk)continue;
  const cx=THREE.MathUtils.clamp(px,c.x-c.halfX,c.x+c.halfX),cz=THREE.MathUtils.clamp(pz,c.z-c.halfZ,c.z+c.halfZ);const ddx=px-cx,ddz=pz-cz,d=Math.hypot(ddx,ddz);
  if(c.kind!=='prop'&&d>1e-4&&d<bestNPd){bestNPd=d;bestNP={c,dx:ddx/d,dz:ddz/d,side:1,dist:d,outer:false};}   // nearest real building face (props excluded)
  if(d>1e-4&&d<bestDist){bestDist=d;best={c,dx:ddx/d,dz:ddz/d,side:1,dist:d,outer:false};}}
 // Climbing / airborne next to a crate, barrel or other low prop (the shop fronts have them): keep the building as the wall, otherwise the climb
 // latches onto the prop's low top, the mantle ends there and the player never reaches the roof.
 if(best&&best.c.kind==='prop'&&bestNP&&(player.climbing||!player.grounded)){best=bestNP;bestDist=bestNP.dist;}
 // The circular outer wall is a wall too (inner face at radius wallRadius-3.5).
 const rr=Math.hypot(px,pz),outerD=(WORLD.wallRadius-3.5)-rr;
 if(rr>1&&outerD<bestDist&&outerD>-.5&&player.pos.y<WORLD.wallHeight-1){bestDist=Math.max(.05,outerD);best={c:{top:WORLD.wallHeight},dx:-px/rr,dz:-pz/rr,side:1,dist:bestDist,outer:true};}
 if(best){const rx=Math.cos(player.yaw),rz=-Math.sin(player.yaw);best.side=(rx*-best.dx+rz*-best.dz)>=0?1:-1;}
 return best;}
function insideXZ(c,x,z,pad=0){return Math.abs(x-c.x)<=c.halfX+pad&&Math.abs(z-c.z)<=c.halfZ+pad;}
// ===================== LEDGE MANTLE (v63): grab the edge, pull up, stand =====================
// The climb used to teleport the player onto the roof. Now a short scripted sequence runs instead:
//   hang (hands reach over the edge)  ->  pull (elbows bend, one knee comes up onto the ledge)  ->  press up and stand.
// The hands / foot are placed with two-bone IK on the ledge, so they stay planted while the body rises past them.
// Tweak: MANTLE.dur / MANTLE.durLow (seconds), MANTLE.forward (how far past the wall edge the body ends up), MANTLE.wallGap (body-to-wall distance while hanging)
const MANTLE={dur:1.25,durLow:.95,forward:.8,wallGap:.32};
const _mq={p:new THREE.Quaternion(),pi:new THREE.Quaternion(),d:new THREE.Quaternion(),t:new THREE.Quaternion()};
const _mv={a:new THREE.Vector3(),b:new THREE.Vector3(),c:new THREE.Vector3(),s:new THREE.Vector3(),h:new THREE.Vector3(),e:new THREE.Vector3(),p:new THREE.Vector3(),k:new THREE.Vector3(),
 F:new THREE.Vector3(),R:new THREE.Vector3(),T:new THREE.Vector3(),pole:new THREE.Vector3(),U:new THREE.Vector3(0,1,0)};
// Push a standing point out of any solid block it overlaps (same rules as the main collision pass) so the mantle ends on valid ground.
function mantleSettle(x,y,z,skip){
 const r=.43;
 for(let it=0;it<5;it++){let moved=false;
  for(const c of colliders){
   if(c.kind==='roof'||c===skip||y>=c.top-.1)continue;if(skip&&skip.virtual&&c.kind==='gable')continue;if(c.bottom&&y+1.65<c.bottom)continue;
   const minX=c.x-c.halfX,maxX=c.x+c.halfX,minZ=c.z-c.halfZ,maxZ=c.z+c.halfZ;
   if(!(x>minX-r&&x<maxX+r&&z>minZ-r&&z<maxZ+r))continue;
   const cx=Math.min(Math.max(x,minX),maxX),cz=Math.min(Math.max(z,minZ),maxZ),dx=x-cx,dz=z-cz,d2=dx*dx+dz*dz;
   if(d2>=r*r)continue;
   if(d2<1e-6){const l=x-minX,rr=maxX-x,t=z-minZ,bb=maxZ-z,m=Math.min(l,rr,t,bb);
    if(m===l)x=minX-r-.02;else if(m===rr)x=maxX+r+.02;else if(m===t)z=minZ-r-.02;else z=maxZ+r+.02;
   }else{const dl=Math.sqrt(d2);x=cx+dx/dl*(r+.02);z=cz+dz/dl*(r+.02);}
   moved=true;
  }
  if(!moved)break;
 }
 return {x,z};
}
function startMantle(wall,low){
 const P=player,c=wall.c,nx=wall.dx,nz=wall.dz,top=c.top;
 // close the gap to the wall so both hands can reach the edge
 const gap=Math.max(0,(wall.dist||MANTLE.wallGap)-MANTLE.wallGap);P.pos.x-=nx*gap;P.pos.z-=nz*gap;
 const M={t:0,dur:low?MANTLE.durLow:MANTLE.dur,low,top,nx,nz,x0:P.pos.x,y0:P.pos.y,z0:P.pos.z,ex:0,ez:0,yEnd:top};
 let ex=M.x0-nx*MANTLE.forward,ez=M.z0-nz*MANTLE.forward;
 const roof=colliders.find(q=>q.kind==='roof'&&q.x===c.x&&q.z===c.z);
 if(roof){const sx=Math.max(.05,roof.halfX-.48),sz=Math.max(.05,roof.halfZ-.48);ex=THREE.MathUtils.clamp(ex,roof.x-sx,roof.x+sx);ez=THREE.MathUtils.clamp(ez,roof.z-sz,roof.z+sz);}
 const st=mantleSettle(ex,top,ez,c);M.ex=st.x;M.ez=st.z;
 const rs=roofSurfaceAt(M.ex,M.ez);if(rs!==null)M.yEnd=Math.max(top,Math.min(rs,top+.6));
 P.mantle=M;P.climbing=true;P.grounded=false;P.onWall=false;P.sliding=false;P.vel.set(0,0,0);P.wallNormal.set(nx,0,nz);P.airTime=0;
}
function finishMantle(){
 const P=player,M=P.mantle;if(!M)return;
 P.pos.set(M.ex,M.yEnd,M.ez);P.vel.set(0,0,0);P.grounded=true;P.climbing=false;P.onWall=false;P.mantle=null;P.spaceLock=true;P.airTime=0;P.coyote=.12;P.wasGrounded=true;P.landImpact=0;
 sound('step');
}
function mantleTick(dt){
 const P=player,M=P.mantle;if(!M)return;
 M.t+=dt;const u=Math.min(1,M.t/M.dur);
 P.vel.set(0,0,0);P.grounded=false;P.climbing=true;P.onWall=false;P.sliding=false;P.airTime=0;
 // fast at first (carries the climb speed), settling as the body comes up over the edge
 const p=1-(1-u)*(1-u);
 const y=M.y0+(M.yEnd-M.y0)*p;
 // the body only moves in over the edge once the chest is above it
 const s=erikaSmoothstep(.42,1,u);
 P.pos.set(M.x0+(M.ex-M.x0)*s,y,M.z0+(M.ez-M.z0)*s);
 if(u>=1)finishMantle();
}
// Rotate `bone` (minimal rotation) so the segment bone->child points along the world direction `dir`; w blends from the current pose.
function mantleAimBone(bone,child,dir,w){
 if(!bone||!child||!bone.parent||w<.002)return;
 bone.parent.updateWorldMatrix(true,false);bone.parent.getWorldQuaternion(_mq.p);
 _mv.a.copy(child.position).normalize().applyQuaternion(bone.quaternion).applyQuaternion(_mq.p);   // bone axis in world space
 _mq.d.setFromUnitVectors(_mv.a,dir);
 _mq.pi.copy(_mq.p).invert();
 _mq.t.copy(_mq.pi).multiply(_mq.d).multiply(_mq.p).multiply(bone.quaternion);
 bone.quaternion.slerp(_mq.t,w);
}
// Two-bone IK (arm or leg): put the end bone on `target` (world), the middle joint pushed toward `pole`.
function mantleLimbIK(upper,lower,end,target,pole,w){
 if(!upper||!lower||!end||w<.002)return;
 upper.getWorldPosition(_mv.s);lower.getWorldPosition(_mv.e);end.getWorldPosition(_mv.h);
 const L1=_mv.s.distanceTo(_mv.e),L2=_mv.e.distanceTo(_mv.h);if(L1<1e-4||L2<1e-4)return;
 _mv.k.copy(target).sub(_mv.s);const d=_mv.k.length();if(d<1e-4)return;_mv.k.multiplyScalar(1/d);
 const dc=Math.min(Math.max(d,Math.abs(L1-L2)+.02),L1+L2-.005);
 const a=(L1*L1-L2*L2+dc*dc)/(2*dc),hh=Math.sqrt(Math.max(0,L1*L1-a*a));
 _mv.p.copy(pole);_mv.p.addScaledVector(_mv.k,-_mv.p.dot(_mv.k));
 if(_mv.p.lengthSq()<1e-6)_mv.p.set(0,0,1).addScaledVector(_mv.k,-_mv.k.z);
 _mv.p.normalize();
 _mv.a.copy(_mv.s).addScaledVector(_mv.k,a).addScaledVector(_mv.p,hh);        // elbow / knee
 _mv.b.copy(_mv.s).addScaledVector(_mv.k,dc);                                  // reachable end point
 _mv.c.copy(_mv.a).sub(_mv.s).normalize();
 mantleAimBone(upper,lower,_mv.c,w);
 lower.getWorldPosition(_mv.e);
 _mv.c.copy(_mv.b).sub(_mv.e);if(_mv.c.lengthSq()<1e-8)return;_mv.c.normalize();
 mantleAimBone(lower,end,_mv.c,w);
}
function mantleLean(list,ang,F){
 _mv.k.copy(_mv.U).cross(F);   // up x forward: positive angle tips the body toward F
 for(const b of list){
  if(!b||!b.parent)continue;
  b.parent.updateWorldMatrix(true,false);b.parent.getWorldQuaternion(_mq.p);
  _mq.d.setFromAxisAngle(_mv.k,ang);_mq.pi.copy(_mq.p).invert();
  _mq.t.copy(_mq.pi).multiply(_mq.d).multiply(_mq.p).multiply(b.quaternion);b.quaternion.copy(_mq.t);
 }
}
const _mHand=[new THREE.Vector3(),new THREE.Vector3()],_mFoot=new THREE.Vector3();
function applyMantlePose(u){
 const P=player,M=P.mantle;if(!M||!erikaPlayer||!erikaPlayer.bones)return;
 const b=erikaPlayer.bones;
 const w=erikaSmoothstep(0,.1,u)*(1-erikaSmoothstep(.86,1,u));
 if(w<.003)return;
 const F=_mv.F.set(-M.nx,0,-M.nz),R=_mv.R.set(-F.z,0,F.x);   // F: toward the wall, R: the character's right
 const hd=MANTLE.wallGap+.26;
 // hands on the top of the ledge, shoulder-width apart; they let go as the body stands up
 const wArm=w*(1-erikaSmoothstep(.74,.93,u));
 for(let i=0;i<2;i++){
  const side=i===0?-1:1;
  _mHand[i].set(M.x0+F.x*hd+R.x*side*.21,M.top+.03,M.z0+F.z*hd+R.z*side*.21);
  _mv.pole.set(0,0,0).addScaledVector(F,-.55).addScaledVector(R,side*.75).addScaledVector(_mv.U,-.25);
  if(i===0)mantleLimbIK(b.leftArm,b.leftForeArm,b.leftHand,_mHand[i],_mv.pole,wArm);
  else mantleLimbIK(b.rightArm,b.rightForeArm,b.rightHand,_mHand[i],_mv.pole,wArm);
 }
 // chest leans over the ledge while pulling, then straightens
 const lean=(.5*erikaSmoothstep(.25,.6,u)-.4*erikaSmoothstep(.6,.95,u))*w;
 mantleLean([b.spine,b.spine1,b.spine2],lean/3,F);
 // right knee comes up and the foot is planted on the ledge, then pushes the body up
 const wLeg=w*erikaSmoothstep(.32,.5,u)*(1-erikaSmoothstep(.8,.97,u));
 if(wLeg>.003){
  _mFoot.set(M.x0+F.x*(hd+.12)+R.x*.17,M.top+.03,M.z0+F.z*(hd+.12)+R.z*.17);
  _mv.pole.set(0,0,0).addScaledVector(F,.9).addScaledVector(_mv.U,.25).addScaledVector(R,.1);
  mantleLimbIK(b.rightUpLeg,b.rightLeg,b.rightFoot,_mFoot,_mv.pole,wLeg);
 }
}

function resolveMovement(prevPos,dt){if(player.mantle){mantleTick(dt);return;}player.onWall=false;const wall=nearWall();const wish=moveInput();const aimingBow=weapon==='bow'&&(bow.aiming||bow.drawing),sprint=(keys.ShiftLeft||keys.ShiftRight)&&!aimingBow;const slashing=!!erikaAnim.attackAction,fast=sprint&&wish.lengthSq()>.1&&!slashing;const slideHeld=!!(keys.KeyC||keys.ControlLeft||keys.ControlRight);if(!slideHeld)player.slideLock=false;player.slideCooldown=Math.max(0,(player.slideCooldown||0)-dt);const wantsSlide=!slashing&&!player.slam&&slideHeld&&!player.slideLock&&player.slideCooldown<=0&&player.grounded&&sprint&&wish.lengthSq()>.1&&Math.hypot(player.vel.x,player.vel.z)>11;
 if(wantsSlide&&!player.sliding){player.sliding=true;player.slideLock=true;player.slideTime=.72;sound('slide');}
 if(player.sliding){player.slideTime-=dt;if(player.slideTime<=0||Math.hypot(player.vel.x,player.vel.z)<2.1||!player.grounded){player.sliding=false;player.slideCooldown=1.5;}}
 let target=fast?13.5:6.8;if(player.sliding||slamLocked())target=0;
 if(slashing){   // slash-walk: slower, with a short step-in as the blade comes through
  const sa=erikaAnim.attackAction,u=sa?Math.min(1,sa.time/Math.max(.1,sa.getClip().duration)):0,rmv=erikaAnim.rootMotion[erikaAnim.attackName],travels=!!(rmv&&rmv.dist>30);if(SWORD_ATK.layered){
   target=4.6*(1-.35*Math.sin(Math.PI*u))*(travels?.55:1);
   if(!travels&&!erikaAnim.lunged&&sa&&sa.time>.12&&wish.lengthSq()>.1){erikaAnim.lunged=true;const fx=-Math.sin(player.yaw),fz=-Math.cos(player.yaw);if(wish.x*fx+wish.z*fz>.3&&player.grounded){player.vel.x+=fx*1.8;player.vel.z+=fz*1.8;}}
  }else{   // full-body slash: the clip's own root motion (applied in computeAttackRootMotion) does the stepping / lunging; input only steers gently
   target=SWORD_ATK.moveSpeed*(1-.5*Math.sin(Math.PI*u))*(travels?SWORD_ATK.travelMul:1);
  }
 }
 if(player.grounded&&!player.sliding){const accel=wish.lengthSq()>.01? (fast?34:25):18;const wx=wish.x*target,wz=wish.z*target;const lam=(slashing&&!SWORD_ATK.layered)?SWORD_ATK.plantRate:accel/8;player.vel.x=THREE.MathUtils.damp(player.vel.x,wx,lam,dt);player.vel.z=THREE.MathUtils.damp(player.vel.z,wz,lam,dt);}else if(!player.sliding){const cableFlight=!!(grapplePull&&grapplePull.active)||hooks.some(h=>h.mode==='attached');const airAccel=!cableFlight&&wish.lengthSq()>.01?3.5:0;player.vel.x+=wish.x*airAccel*dt;player.vel.z+=wish.z*airAccel*dt;const maxAir=18;const hs=Math.hypot(player.vel.x,player.vel.z);if(hs>maxAir){player.vel.x*=maxAir/hs;player.vel.z*=maxAir/hs;}}
 if(player.sliding){player.vel.x*=Math.pow(.989,dt*60);player.vel.z*=Math.pow(.989,dt*60);}
 // Fast climb: face any building and hold W + SPACE to scale it without a cable.
 player.climbing=false;
 if(wall&&!player.slam&&!wall.outer&&keys.Space&&!player.spaceLock&&!(grapplePull&&grapplePull.active)&&hooks.every(h=>h.mode==='ready')){
  const toward=wish.x*-wall.dx+wish.z*-wall.dz;
  if(keys.KeyW&&toward>.45&&wall.c.top>player.pos.y+.3){
   player.climbing=true;player.grounded=false;player.sliding=false;player.wallSide=wall.side;player.wallNormal.set(wall.dx,0,wall.dz);
   player.vel.x=-wall.dx*1.2;player.vel.z=-wall.dz*1.2;player.vel.y=THREE.MathUtils.damp(player.vel.y,CLIMB_SPEED,14,dt);
   player.airTime=0;
   if(wall.c.top-player.pos.y<1.9){startMantle(wall,false);return;}   // reached the ledge: grab it, pull up and stand (see MANTLE)
  }
 }
 if(player.grounded){player.wallLock=null;player.wallBlock=null;}
 // One face only: if the wall under the runner changes (corner of a building), the wall run ends and the player falls; that building cannot be wall-run again until landing.
 let wrWall=wall;
 if(wrWall&&!wrWall.outer){
  const bl=player.wallBlock,lk=player.wallLock;
  if(bl&&bl.includes(wrWall.c))wrWall=null;
  else if(lk&&(wrWall.c!==lk.c||wrWall.dx*lk.dx+wrWall.dz*lk.dz<.9)){player.wallBlock=(bl||[]).concat([lk.c,wrWall.c]);wrWall=null;}
 }
 // Wall run works on any wall (buildings from any side, corners, and the outer city wrWall) in either direction.
 if(wrWall&&!player.slam&&!player.climbing&&!player.grounded&&player.airTime>.04&&Math.abs(player.vel.y)<9&&wish.lengthSq()>.05){const tangent=new THREE.Vector3(-wrWall.dz,0,wrWall.dx);const dot=player.vel.x*tangent.x+player.vel.z*tangent.z;const wishDot=wish.x*tangent.x+wish.z*tangent.z;
  const towardWall=wish.x*-wrWall.dx+wish.z*-wrWall.dz;
  if(Math.abs(wishDot)>.3||Math.abs(dot)>3.5){const dirSign=Math.abs(wishDot)>.3?Math.sign(wishDot):Math.sign(dot)||1;const runSpd=Math.max(8,Math.abs(dot),fast?11:0);
   if(!wrWall.outer&&!player.wallLock)player.wallLock={c:wrWall.c,dx:wrWall.dx,dz:wrWall.dz};player.onWall=true;player.wallSide=wrWall.side;player.wallNormal.set(wrWall.dx,0,wrWall.dz);player.wallTime+=dt;
   player.vel.x=THREE.MathUtils.damp(player.vel.x,tangent.x*dirSign*runSpd-wrWall.dx*1.5,7,dt);player.vel.z=THREE.MathUtils.damp(player.vel.z,tangent.z*dirSign*runSpd-wrWall.dz*1.5,7,dt);
   player.vel.y=Math.max(player.vel.y,-1.3)+.4*dt;{const pk=(WALLRUN_POSE.wallDist-wrWall.dist)*(1-Math.exp(-14*dt));player.pos.x+=wrWall.dx*pk;player.pos.z+=wrWall.dz*pk;}}}
 if(!player.onWall){player.wallTime=0;player.wallLock=null;}
 // Pull and rope constraints. Each cable contributes independently, so dual anchors bend the path naturally.
 for(const h of hooks){if(h.mode!=='attached'||!h.anchor||(grapplePull&&grapplePull.active&&h.autoPull))continue;const hand=getHandWorld(h.side);const delta=h.anchor.clone().sub(hand);const dist=delta.length();if(dist>h.length){const dir=delta.normalize();const excess=dist-h.length;player.vel.addScaledVector(dir,Math.min(40,excess*13)*dt);if(excess>1.2){player.pos.addScaledVector(dir,Math.min(excess*.16,2.2));const outward=player.vel.dot(dir);if(outward<0)player.vel.addScaledVector(dir,-outward);}}}
 if(player.kick)kickUpdate(dt);if(grapplePull&&grapplePull.active){const delta=grapplePull.target.clone().sub(player.pos);const distance=delta.length();if(!Number.isFinite(distance)){detachAll(false);showToast('GRAPPLE RESET');}else if(distance<1.35){player.pos.copy(grapplePull.target);player.vel.multiplyScalar(.48);detachAll(false);showToast('TARGET REACHED');}else{const desiredSpeed=THREE.MathUtils.clamp(distance*6.2,18,78);const desired=delta.normalize().multiplyScalar(desiredSpeed);player.vel.lerp(desired,1-Math.exp(-18*dt));player.grounded=false;player.sliding=false;player.onWall=false;}}
 // WASD gently redirects the airborne travel path toward the requested landing area without changing its speed or animation.
 const cableFlight=!!(grapplePull&&grapplePull.active)||hooks.some(h=>h.mode==='attached');
 if(!player.grounded&&!player.climbing&&!player.onWall&&!player.sliding){
  const airWish=moveInput(),hs=Math.hypot(player.vel.x,player.vel.z);
  if(airWish.lengthSq()>.01&&hs>.1){
   const currentHeading=Math.atan2(player.vel.x,player.vel.z),targetHeading=Math.atan2(airWish.x,airWish.z);
   const headingDelta=Math.atan2(Math.sin(targetHeading-currentHeading),Math.cos(targetHeading-currentHeading));
   const steerRate=cableFlight?.72:.9,nextHeading=currentHeading+THREE.MathUtils.clamp(headingDelta,-steerRate*dt,steerRate*dt);
   player.vel.x=Math.sin(nextHeading)*hs;player.vel.z=Math.cos(nextHeading)*hs;
  }
 }
 // Gravity and movement integration
 if(!player.grounded&&!player.climbing){player.vel.y-=(grapplePull&&grapplePull.active?1.5:(player.onWall?3.2:24))*dt; if(player.onWall)player.vel.y=Math.max(player.vel.y,-2.2);}else if(player.vel.y<0)player.vel.y=0;
 const wasGroundedBeforeMove=player.grounded;const before=player.pos.clone();player.pos.addScaledVector(player.vel,dt);player.pos.add(attackRootDisp);
 // Hard circular boundary on the inside of the defensive wall.
 const radial=Math.hypot(player.pos.x,player.pos.z);const maxR=WORLD.wallRadius-4.3;if(radial>maxR){const norm=new THREE.Vector3(player.pos.x,0,player.pos.z).normalize();player.pos.x=norm.x*maxR;player.pos.z=norm.z*maxR;const outward=player.vel.dot(norm);if(outward>0)player.vel.addScaledVector(norm,-outward);}
 // Roof colliders provide floor support only; they must not become invisible side walls.
 const _rsHere=roofSurfaceAt(player.pos.x,player.pos.z);   // sloped-roof height under the player (null = no roof here)
 for(const c of colliders){if(c.kind==='roof')continue;
  // The gable boxes only stop you walking into the triangular end wall. Someone already on the sloped roof plane (walking up toward the ridge) must never be pushed back by them.
  if(c.kind==='gable'&&_rsHere!==null&&player.pos.y>=_rsHere-.45)continue;
  const minX=c.x-c.halfX,maxX=c.x+c.halfX,minZ=c.z-c.halfZ,maxZ=c.z+c.halfZ;
  const bodyBottom=player.pos.y,bodyTop=player.pos.y+(player.sliding?.9:1.65);if(bodyTop<.03||bodyBottom>c.top+.3)continue;if(c.bottom&&bodyTop<c.bottom)continue;
  // Let a descending player cross the roof plane this frame; landing is resolved immediately afterwards.
  if(player.vel.y<=0&&before.y>=c.top-.12&&player.pos.y<=c.top+.03&&insideXZ(c,player.pos.x,player.pos.z,.05))continue;
  // Above the actual building top, horizontal movement is unobstructed.
  if(player.pos.y>=c.top-.1)continue;
  const closestX=THREE.MathUtils.clamp(player.pos.x,minX,maxX),closestZ=THREE.MathUtils.clamp(player.pos.z,minZ,maxZ);const dx=player.pos.x-closestX,dz=player.pos.z-closestZ;const distSq=dx*dx+dz*dz;const radius=.43;if(distSq<radius*radius){let nx=dx,nz=dz;if(distSq<.0001){const pX=Math.min(Math.abs(player.pos.x-minX),Math.abs(maxX-player.pos.x));const pZ=Math.min(Math.abs(player.pos.z-minZ),Math.abs(maxZ-player.pos.z));if(pX<pZ)nx=player.pos.x-c.x<0?-1:1;else nz=player.pos.z-c.z<0?-1:1;}const len=Math.hypot(nx,nz)||1;player.pos.x=closestX+nx/len*radius;player.pos.z=closestZ+nz/len*radius;const vn=player.vel.x*nx/len+player.vel.z*nz/len;if(vn<0){player.vel.x-=vn*nx/len;player.vel.z-=vn*nz/len;}}
 }
 // Monsters occupy space so the player cannot walk through an attack.
 for(const m of monsters){if(!m.alive)continue;const dx=player.pos.x-m.root.position.x,dz=player.pos.z-m.root.position.z,distSq=dx*dx+dz*dz,minDist=.43+.40*m.cfg.scale;if(distSq<minDist*minDist&&player.pos.y<m.cfg.scale*2.7){const dist=Math.sqrt(distSq)||1,nx=dx/dist,nz=dz/dist;player.pos.x=m.root.position.x+nx*minDist;player.pos.z=m.root.position.z+nz*minDist;const vn=player.vel.x*nx+player.vel.z*nz;if(vn<0){player.vel.x-=vn*nx;player.vel.z-=vn*nz;}}}
 // Landing and rooftop/floor detection; select the highest surface crossed in this frame.
 let landedY=0;const oldY=before.y;let newY=player.pos.y;let candidate=0;
 if(newY<=.0&&oldY>=-.3)candidate=0;
 for(const c of colliders){if(c.kind==='gable'||c.noStand||!insideXZ(c,player.pos.x,player.pos.z,.05))continue;const top=c.top;if(oldY>=top-.12&&newY<=top+.03&&player.vel.y<=0&&top>candidate)candidate=top;}
 let roofTop=roofSurfaceAt(player.pos.x,player.pos.z);for(const c of colliders){if(c.kind==='roof'&&insideXZ(c,player.pos.x,player.pos.z,.05)&&(roofTop===null||c.top>roofTop))roofTop=c.top;}const horizontalStep=Math.hypot(player.pos.x-before.x,player.pos.z-before.z);if(roofTop!==null&&wasGroundedBeforeMove&&roofTop>=oldY-.55&&roofTop<=oldY+Math.max(.55,horizontalStep*1.4+.16)){player.pos.y=roofTop;newY=roofTop;if(roofTop>candidate)candidate=roofTop;}if(roofTop!==null&&oldY>=roofTop-.12&&newY<=roofTop+.03&&player.vel.y<=0&&roofTop>candidate)candidate=roofTop;
 if(newY<=candidate&&player.vel.y<=0){landedY=candidate;const fall=Math.abs(player.vel.y);player.pos.y=landedY;if(!player.grounded){player.grounded=true;player.coyote=.12;player.landImpact=fall;player.landEvent++;try{sfxLand(fall);}catch(e){}if(fall>8){player.landTime=.34;player.vel.x*=.78;player.vel.z*=.78;if(fall>14){player.vel.x*=.8;player.vel.z*=.8;}}}player.vel.y=0;player.airTime=0;}
 else{if(player.grounded&&newY>landedY+.04)player.grounded=false;if(!player.grounded)player.airTime+=dt;}
 // Mantle: jump near a low ledge to pull the body to its top rather than snagging on the side.
 if(!player.grounded&&keys.Space&&!player.spaceLock&&wall&&!wall.outer&&wall.c.top>player.pos.y+.35&&wall.c.top<player.pos.y+2.25&&player.vel.y<1){const forward=moveInput();if(forward.lengthSq()>.1&&forward.x*-wall.dx+forward.z*-wall.dz>.2){startMantle(wall,true);}}
 if(player.pos.y<-20){resetPlayer();showToast('RETURNED TO TRAINING GROUND');}
 player.wasGrounded=player.grounded;
}
function erikaRootAt(rm,t,out){
 const ts=rm.times,n=ts.length;if(t<=ts[0]){out.x=rm.x[0];out.z=rm.z[0];return out;}if(t>=ts[n-1]){out.x=rm.x[n-1];out.z=rm.z[n-1];return out;}
 let i=0;while(i<n-2&&t>ts[i+1])i++;const u=(t-ts[i])/(ts[i+1]-ts[i]);out.x=rm.x[i]+(rm.x[i+1]-rm.x[i])*u;out.z=rm.z[i]+(rm.z[i+1]-rm.z[i])*u;return out;
}
const _rmA={x:0,z:0},_rmB={x:0,z:0};
// Travel the slash clip would make during the next mixer step, in world space (forward = player facing).
function computeAttackRootMotion(dt){
 attackRootDisp.set(0,0,0);
 const A=erikaAnim,act=A.attackAction,rm=act&&A.rootMotion[A.attackName];if(!rm||!player.grounded||!erikaPlayer||!erikaPlayer.root)return;
 const dur=act.getClip().duration,t0=act.time,t1=Math.min(dur,t0+Math.min(dt,.1)*act.getEffectiveTimeScale());if(t1<=t0)return;
 erikaRootAt(rm,t0,_rmA);erikaRootAt(rm,t1,_rmB);
 const ws=erikaPlayer.root.getWorldScale(_rmV).x,hipsRest=A.attackRootPosition?A.attackRootPosition.y:rm.y0;
 let ratio=hipsRest/rm.y0;if(!(ratio>.5&&ratio<2))ratio=1;           // this character's legs vs. the legs the clip was made for -> feet do not slide
 const k=ws*ratio,dz=(_rmB.z-_rmA.z)*k,dx=(_rmB.x-_rmA.x)*k,sy=Math.sin(player.yaw),cy=Math.cos(player.yaw);
 attackRootDisp.set(-sy*dz-cy*dx,0,-cy*dz+sy*dx);                      // model +z = forward, model +x = the character's left
}
const _rmV=new THREE.Vector3();
function updateMovement(dt){if(playerDeath.active)playerDeathTick(dt);const swordAttackBusy=!!erikaAnim.attackAction||!!player.lunge||!!player.block||rollLocked();computeAttackRootMotion(dt);if(swordAttackBusy){player.jumpBuffer=0;player.sliding=false;}player.jumpBuffer=swordAttackBusy?0:Math.max(0,player.jumpBuffer-dt);if(player.grounded)player.coyote=.12;else player.coyote=Math.max(0,player.coyote-dt);
 if(player.grounded||player.onWall||player.climbing||(grapplePull&&grapplePull.active)||hooks.some(h=>h.mode!=='ready'))player.gJump=false;   // only a plain jump from the ground allows the leap strike
 if(!swordAttackBusy&&!player.mantle&&!slamLocked()&&player.jumpBuffer>0&&(player.grounded||player.coyote>0||player.onWall)){player.gJump=!player.onWall;player.vel.y=player.onWall?10.5:9.5;const direction=moveInput();player.vel.x+=direction.x*(keys.ShiftLeft?3:1.5)+(player.onWall?player.wallNormal.x*7:0);player.vel.z+=direction.z*(keys.ShiftLeft?3:1.5)+(player.onWall?player.wallNormal.z*7:0);player.grounded=false;player.onWall=false;player.airTime=.01;player.jumpBuffer=0;player.sliding=false;sound('jump');}
 lungeSafe(lungeUpdate,dt);slamSafe(slamPre,dt);const oldPos=player.pos.clone();fallRollTick(dt);if(player.dash)dashTick(dt);else if(player.lunge)lungeSafe(lungeMove,dt);else if(CHG.down&&CHG.air&&!player.grounded)lungeSafe(lungeAirHold,dt);else if(player.block)lungeSafe(blockMove,dt);else if(rollLocked())fallRollSafe(dt,oldPos);else if(superFlying())superFlySafe(dt);else resolveMovement(oldPos,dt);fallRollCheck();slamSafe(slamPost,dt);
 // Eye height tracks the real slide posture.
 const eyeTarget=rollLocked()?0.75:(player.sliding?0.86:1.65);player.eye=THREE.MathUtils.damp(player.eye,eyeTarget,player.sliding?16:10,dt);
 const horizontalSpeed=Math.hypot(player.vel.x,player.vel.z);player.moveSpeed=horizontalSpeed;
 if(grapplePull&&grapplePull.active)player.state='GRAPPLING';else if(hooks.some(h=>h.mode==='flying'))player.state='HOOK LAUNCH';else if(player.climbing)player.state='CLIMBING';else if(player.onWall)player.state='WALL RUN';else if(player.sliding)player.state='SLIDING';else if(!player.grounded)player.state=player.vel.y>1.2?'RISING':'FALLING';else if(horizontalSpeed>.8)player.state=(keys.ShiftLeft||keys.ShiftRight)&&!(weapon==='bow'&&(bow.aiming||bow.drawing))?'SPRINTING':'RUNNING';else player.state='IDLE';
 // Rope-flight pose persists after releasing the cable in mid-air, all the way down until landing / wall contact.
 if(player.state==='GRAPPLING'||player.state==='HOOK LAUNCH')player.postFlight=!player.grounded||player.state==='HOOK LAUNCH'?true:false;else if(player.grounded||player.onWall||player.climbing)player.postFlight=false;
 // Small footstep cadence, synced with horizontal movement.
 if(player.grounded&&horizontalSpeed>2){player.stepTime-=dt;if(player.stepTime<=0){sound('step');player.stepTime=player.sliding?.25:(horizontalSpeed>9?.28:.42);}}else{player.stepTime=.1;stopRunFootsteps();}
 animateBody(dt);animateErika(dt);syncPlayerVisuals(dt);ui.movement.textContent=player.state;
}
function animateBody(dt){
 const speed=player.moveSpeed,groundMove=player.grounded&&!player.sliding&&speed>.75;
 const sprinting=player.state==='SPRINTING',grappling=player.state==='GRAPPLING'||!!player.postFlight,launching=player.state==='HOOK LAUNCH';
 const moveBlend=THREE.MathUtils.clamp(speed/(sprinting?13.5:8),0,1);
 const strideRate=grappling?17+Math.min(speed,55)*.075:player.onWall?11.8:groundMove?(sprinting?12.8:7.2+moveBlend*3.2):player.sliding?10:(!player.grounded?4.5:1.8);
 walkBob+=dt*strideRate;
 const wave=Math.sin(walkBob),wave2=Math.cos(walkBob),phase=walkBob;
 const landing=THREE.MathUtils.clamp(player.landTime/.34,0,1);player.landTime=Math.max(0,player.landTime-dt);
 // Head/torso impulse and camera bob make starts, hard landings, and cable acceleration readable.
 let leanX=0,leanZ=0;
 if(sprinting)leanX=-.17;else if(groundMove)leanX=-.075*moveBlend;else if(player.sliding)leanX=-.23;else if(grappling||launching)leanX=-.31;else if(!player.grounded)leanX=player.vel.y>1?.06:.12;
 if(player.onWall)leanZ=-player.wallSide*.16;
 else if(grappling){const right=new THREE.Vector3(Math.cos(player.yaw),0,-Math.sin(player.yaw));leanZ=THREE.MathUtils.clamp(player.vel.dot(right)*.008,-.12,.12);}
 const torsoY=1.16+(groundMove?Math.abs(wave)*.045*moveBlend:0)+(Math.sin(elapsed*2.1)*.008)-landing*.045;
 torso.position.y=THREE.MathUtils.damp(torso.position.y,torsoY,18,dt);
 torso.rotation.x=THREE.MathUtils.damp(torso.rotation.x,leanX+(player.grounded?Math.sin(elapsed*2.3)*.018:0),11,dt);
 torso.rotation.z=THREE.MathUtils.damp(torso.rotation.z,leanZ+(player.sliding?-.12:0),12,dt);
 torso.scale.y=THREE.MathUtils.damp(torso.scale.y,1-landing*.055,18,dt);
 // Camera rhythm is restrained at speed, but clearly distinct for sprinting and cable flight.
 let bobTarget=0;
 if(player.grounded&&groundMove)bobTarget=Math.abs(wave)*(sprinting?.052:.027)*moveBlend;
 else if(player.sliding)bobTarget=.012+Math.sin(phase)*.008;
 else if(player.onWall)bobTarget=.022+Math.sin(phase)*.016;
 else if(grappling||launching)bobTarget=Math.sin(phase*.55)*.016;
 else if(!player.grounded)bobTarget=Math.sin(elapsed*4.6)*.009;
 else bobTarget=Math.sin(elapsed*1.8)*.003;
 viewBob=THREE.MathUtils.damp(viewBob,bobTarget,18,dt);
 let rollTarget=player.onWall?-player.wallSide*.055:grappling?THREE.MathUtils.clamp(player.vel.dot(new THREE.Vector3(Math.cos(player.yaw),0,-Math.sin(player.yaw)))*.0025,-.075,.075):0;
 viewRoll=THREE.MathUtils.damp(viewRoll,rollTarget,7,dt);
 // Arms: opposing run swing, deeper sprint drive, low slide brace, and fully extended grappling pose.
 for(const a of arms){
  const side=a.side,armPhase=wave*(-side);let upperX=.43,upperZ=side*.13,elbowX=.27,handX=0,handZ=side*.04;
  if(groundMove){upperX=.43+armPhase*(sprinting?.92:.62)*moveBlend;upperZ=side*(.12+(sprinting?.04:0));elbowX=.28+Math.max(0,armPhase)*.38;handX=-.06+armPhase*.08;}
  if(player.sliding){upperX=.98+Math.sin(phase)*.06;upperZ=side*.30;elbowX=.24;handX=-.12;}
  if(player.onWall){upperX=.72+Math.sin(phase*1.2)*.12;upperZ=side*.55;elbowX=.45+Math.max(0,armPhase)*.18;handX=.12;}
  if(!player.grounded&&!grappling&&!launching){upperX=player.vel.y>1?.78:.56;upperZ=side*(.48+Math.sin(phase+side)*.08);elbowX=player.vel.y>1?.1:.42;handX=.12;}
  if(launching){upperX=1.26;upperZ=side*.22;elbowX=-.08;handX=-.18;handZ=side*.08;}
  if(grappling){upperX=1.47+Math.sin(phase*.7+side)*.07;upperZ=side*.17;elbowX=-.16+Math.sin(phase+side)*.035;handX=-.22;handZ=side*.06;}
  if(!groundMove&&!player.sliding&&!player.onWall&&!grappling&&!launching&&!player.grounded){upperZ=side*.5;}
  a.upper.rotation.x=THREE.MathUtils.damp(a.upper.rotation.x,upperX,grappling?18:13,dt);
  a.upper.rotation.z=THREE.MathUtils.damp(a.upper.rotation.z,upperZ,13,dt);
  a.upper.rotation.y=THREE.MathUtils.damp(a.upper.rotation.y,grappling?-.06:Math.sin(phase*.5+side)*.025,8,dt);
  a.elbow.rotation.x=THREE.MathUtils.damp(a.elbow.rotation.x,elbowX,14,dt);
  a.elbow.rotation.z=THREE.MathUtils.damp(a.elbow.rotation.z,side*(grappling?.04:.02),12,dt);
  a.hand.rotation.x=THREE.MathUtils.damp(a.hand.rotation.x,handX,16,dt);
  a.hand.rotation.z=THREE.MathUtils.damp(a.hand.rotation.z,handZ,12,dt);
  a.shoulder.rotation.z=THREE.MathUtils.damp(a.shoulder.rotation.z,side*(sprinting?.08:grappling?.14:0),10,dt);
 }
 // Legs now have a real alternating stride, active knee lift, sprint tuck, airborne trail and cable-flight tuck.
 for(const l of legs){
  const side=l.side,legPhase=wave*side;let legX=0,kneeX=.08,legZ=side*.015,bootX=0;
  if(groundMove){const amp=sprinting?.9:.62;legX=legPhase*amp*moveBlend;kneeX=.12+Math.max(0,-legPhase)*(sprinting?1.02:.78)*moveBlend;bootX=-legX*.18;}
  else if(player.sliding){legX=.88+Math.sin(phase+side)*.08;kneeX=.72;bootX=-.15;}
  else if(player.onWall){legX=legPhase*.82;kneeX=.62+Math.max(0,-legPhase)*.42;bootX=-legX*.15;}
  else if(grappling||launching){legX=-.48+legPhase*.17;kneeX=.86+Math.max(0,legPhase)*.18;legZ=side*.11;bootX=.12;}
  else if(!player.grounded){legX=player.vel.y>1?-.22+legPhase*.22:.18+legPhase*.27;kneeX=player.vel.y>1?.64:.42+Math.max(0,-legPhase)*.2;bootX=-.08;}
  else {legX=Math.sin(phase*.5+side)*.018;kneeX=.08+Math.sin(elapsed*2+side)*.02;}
  kneeX+=landing*.7;
  l.leg.rotation.x=THREE.MathUtils.damp(l.leg.rotation.x,legX,grappling?12:15,dt);
  l.leg.rotation.z=THREE.MathUtils.damp(l.leg.rotation.z,legZ,12,dt);
  l.knee.rotation.x=THREE.MathUtils.damp(l.knee.rotation.x,kneeX,16,dt);
  l.boot.rotation.x=THREE.MathUtils.damp(l.boot.rotation.x,bootX,15,dt);
 }
 for(const t of waistTails){const side=t.side;const targetX=grappling?-.38:player.sliding?.4:player.onWall?.16:groundMove?Math.sin(phase+side)*.18:!player.grounded?-.25:Math.sin(elapsed*2+side)*.025;t.group.rotation.x=THREE.MathUtils.damp(t.group.rotation.x,targetX,7,dt);t.group.rotation.z=THREE.MathUtils.damp(t.group.rotation.z,side*(grappling?.15:Math.sin(phase*.7+side)*.08),8,dt);}
}
function updateEffects(dt){slamSafe(updateSlamFx,dt);slamSafe(superFxUpdate,dt);slamSafe(dashFxUpdate,dt);lungeSafe(lungeFxUpdate,dt);lungeSafe(blockFxUpdate,dt);slamSafe(swordHitFxUpdate,dt);slamSafe(captiveUpdate,dt);slamSafe(weaponHudUpdate,dt);if(!dustMesh||!dustDummy)return;for(let i=0;i<dustParticles.length;i++){const p=dustParticles[i];if(p.active){p.life-=dt;if(p.life<=0){p.active=false;}else{p.pos.addScaledVector(p.vel,dt);const fade=Math.max(0,p.life/p.maxLife);dustDummy.position.copy(p.pos);dustDummy.scale.setScalar(p.size*(.35+.65*fade));dustDummy.updateMatrix();dustMesh.setMatrixAt(i,dustDummy.matrix);continue;}}dustDummy.position.set(0,-1000,0);dustDummy.scale.setScalar(0);dustDummy.updateMatrix();dustMesh.setMatrixAt(i,dustDummy.matrix);}dustMesh.instanceMatrix.needsUpdate=true;}
function spawnDust(){if(!dustMesh)return;let created=0;for(let i=0;i<dustParticles.length&&created<(GFX.fxM>=1?3:GFX.fxM>.5?2:1);i++){const p=dustParticles[i];if(p.active)continue;p.active=true;p.pos.set(player.pos.x+(Math.random()-.5)*.8,player.pos.y+.1,player.pos.z+(Math.random()-.5)*.8);p.vel.set((Math.random()-.5)*1,Math.random()*1.2,(Math.random()-.5)*1);p.life=p.maxLife=.34;p.size=.07+Math.random()*.09;created++;}}
function updateFps(dt){frames++;fpsAt+=dt;if(fpsAt>=.5){fpsNow=Math.round(frames/fpsAt);frames=0;fpsAt=0;ui.fps.textContent='FPS '+fpsNow;}}
// ===================== WAVE PANEL (top right): current wave, monsters remaining, monsters slain =====================
function waveHudUpdate(){
 {const ac=document.getElementById('ammoCross');if(ac){const on=weapon==='bow'&&running,k=on?AMMO.cur+'/'+AMMO.max:'';if(ac._k!==k){ac._k=k;ac.classList.toggle('on',on);ac.classList.toggle('empty',on&&AMMO.cur<=0);ac.innerHTML=on?'&#10148; '+AMMO.cur+'<small>/'+AMMO.max+'</small>':'';}}}
 const el=document.getElementById('waveHUD');if(!el)return;
 const q=c=>el.querySelector(c),W=WAVES,total=Math.max(1,waveCount(W.n)),left=Math.max(0,W.left||0),brk=W.state==='break';
 const key=[W.n,left,monsterKills,AMMO.cur,AMMO.max,brk,brk?Math.ceil(Math.max(0,W.breakT)):0].join('|');
 if(key===el._k)return;el._k=key;
 q('.wv-num').textContent=W.n;q('.wv-left').textContent=brk?0:left;q('.wv-slain').textContent=monsterKills;{const am=q('.wv-ammo');am.textContent=AMMO.cur+'/'+AMMO.max;am.style.color=AMMO.cur<=0?'#ff5a4a':'';}
 q('.wv-bar i').style.width=(brk?100:Math.max(0,Math.min(1,1-left/total))*100).toFixed(1)+'%';
 el.dataset.state=brk?'break':'fight';
 q('.wv-note').textContent=brk?'WAVE CLEARED // NEXT IN '+Math.ceil(Math.max(0,W.breakT))+'s':'';
}
// ===================== MINIMAP (bottom right): districts, streets, buildings, wall, monsters, the captive and you =====================
// Tweak: MM.fps (redraws per second), MM.css (size in px; also change #miniMap / .mm-frame in the CSS). Up on the map = -Z (the gate side).
const MM={el:null,cv:null,ctx:null,stat:null,S:0,SS:0,sc:1,dpr:1,css:245,z:1.5,fps:30,t:0,err:0,shown:null};
// The map is centred on you and rotates with the camera: whatever you are looking at is always UP on the map.
// Tweak: MM.z (zoom: 1 = whole city), MM.fps (redraws per second), MM.css (size in px; also change #miniMap / .mm-frame in the CSS).
function mmInit(){
 MM.el=document.getElementById('miniMap');MM.cv=document.getElementById('mmCanvas');if(!MM.el||!MM.cv)throw new Error('minimap markup missing');
 MM.dpr=Math.min(3,Math.max(1,window.devicePixelRatio||1));MM.S=Math.round(MM.css*MM.dpr);MM.cv.width=MM.cv.height=MM.S;MM.ctx=MM.cv.getContext('2d');
 MM.SS=Math.round(MM.S*MM.z);MM.sc=(MM.S/2-3*MM.dpr)/(WORLD.wallRadius+5)*MM.z;   // sc = canvas px per world metre
}
function mmBuildStatic(){
 const S=MM.SS,sc=MM.sc,d=MM.dpr,c=document.createElement('canvas');c.width=c.height=S;const g=c.getContext('2d');
 const P=(x,z)=>[S/2+x*sc,S/2+z*sc];
 g.save();g.beginPath();g.arc(S/2,S/2,S/2-1,0,Math.PI*2);g.clip();
 g.fillStyle='#1b2620';g.fillRect(0,0,S,S);
 g.beginPath();g.arc(S/2,S/2,(WORLD.wallRadius-3.5)*sc,0,Math.PI*2);g.fillStyle='#2f4332';g.fill();            // grass inside the wall
 const cxs=[-88,0,88];
 for(let i=0;i<6;i++){const cx=cxs[i%3],cz=i<3?-60:60,[x,y]=P(cx-39,cz-39);                                      // the six districts
  g.fillStyle=i%2?'#5e594f':'#6c6659';g.fillRect(x,y,78*sc,78*sc);g.strokeStyle='rgba(240,196,110,.45)';g.lineWidth=Math.max(1,d*1.2);g.strokeRect(x,y,78*sc,78*sc);}
 g.fillStyle='#bcb092';                                                                                          // the two main streets
 {const [x,y]=P(-141,-12.5);g.fillRect(x,y,280*sc,25*sc);}{const [x,y]=P(-12.5,-120);g.fillRect(x,y,25*sc,240*sc);}
 g.strokeStyle='rgba(70,60,44,.6)';g.lineWidth=Math.max(1,d*.9);g.setLineDash([5*d,5*d]);g.beginPath();
 {const a=P(-141,0),b=P(139,0);g.moveTo(a[0],a[1]);g.lineTo(b[0],b[1]);}{const a=P(0,-120),b=P(0,120);g.moveTo(a[0],a[1]);g.lineTo(b[0],b[1]);}g.stroke();g.setLineDash([]);
 {const [x,y]=P(0,0);g.beginPath();g.arc(x,y,12*sc,0,Math.PI*2);g.fillStyle='#cfc7ae';g.fill();g.lineWidth=Math.max(1,d*1.1);g.strokeStyle='rgba(60,50,36,.75)';g.stroke();   // plaza + fountain
  g.beginPath();g.arc(x,y,4*sc,0,Math.PI*2);g.fillStyle='#74b3d1';g.fill();}
 g.lineWidth=Math.max(1,d*1.1);
 for(const k of colliders){if(k.kind!=='building')continue;const [x,y]=P(k.x-k.halfX,k.z-k.halfZ),w=k.halfX*2*sc,h=k.halfZ*2*sc;   // buildings
  g.fillStyle='#e2c99f';g.fillRect(x,y,w,h);g.strokeStyle='rgba(30,22,12,.9)';g.strokeRect(x,y,w,h);}
 g.beginPath();g.arc(S/2,S/2,WORLD.wallRadius*sc,0,Math.PI*2);g.lineWidth=7*sc;g.strokeStyle='#a29e92';g.stroke();                                // city wall
 g.lineWidth=Math.max(1,d*1.1);g.strokeStyle='rgba(0,0,0,.65)';
 for(const r of [WORLD.wallRadius-3.5,WORLD.wallRadius+3.5]){g.beginPath();g.arc(S/2,S/2,r*sc,0,Math.PI*2);g.stroke();}
 {const [x,y]=P(0,-WORLD.wallRadius);g.fillStyle='#f0c577';g.fillRect(x-7*sc,y-4.5*sc,14*sc,9*sc);g.strokeStyle='rgba(0,0,0,.8)';g.strokeRect(x-7*sc,y-4.5*sc,14*sc,9*sc);}   // gate
 g.restore();MM.stat=c;   // (district / gate labels are drawn upright every frame, see minimapUpdate)
}
function minimapUpdate(dt){
 if(!MM.el)mmInit();
 const show=!!(running&&!playerDeath.active&&worldBuilt);
 if(MM.shown!==show){MM.shown=show;MM.el.style.display=show?'block':'none';}
 if(!show)return;
 MM.t-=dt;if(MM.t>0)return;MM.t=1/MM.fps;
 if(!MM.stat)mmBuildStatic();
 const g=MM.ctx,S=MM.S,sc=MM.sc,d=MM.dpr,now=performance.now(),TAU=Math.PI*2,half=S/2,Rv=half-1,lim=Rv-9*d;
 const yaw=player.yaw,cs=Math.cos(yaw),sn=Math.sin(yaw),ox=player.pos.x,oz=player.pos.z;
 const toS=(x,z)=>{const dx=(x-ox)*sc,dz=(z-oz)*sc;return [half+dx*cs-dz*sn,half+dx*sn+dz*cs];};            // world -> map (you in the centre, your view direction = up)
 const edge=(x,z)=>{const p=toS(x,z);let dx=p[0]-half,dy=p[1]-half;const r=Math.hypot(dx,dy);if(r>lim){dx*=lim/r;dy*=lim/r;return [half+dx,half+dy,true];}return [p[0],p[1],false];};   // far things stick to the rim
 g.clearRect(0,0,S,S);
 g.save();g.beginPath();g.arc(half,half,Rv,0,TAU);g.clip();
 g.fillStyle='#1b2620';g.fillRect(0,0,S,S);
 g.save();g.translate(half,half);g.rotate(yaw);g.drawImage(MM.stat,-ox*sc-MM.SS/2,-oz*sc-MM.SS/2);g.restore();   // the rotating map
 g.textAlign='center';g.textBaseline='middle';g.lineJoin='round';g.fillStyle='rgba(255,246,222,.96)';g.strokeStyle='rgba(0,0,0,.85)';g.lineWidth=3.2*d;
 {const cxs=[-88,0,88];g.font='700 '+(12*d)+'px Rajdhani,system-ui,sans-serif';
  for(let i=0;i<6;i++){const p=toS(cxs[i%3],i<3?-60:60);if(Math.hypot(p[0]-half,p[1]-half)<lim-6*d){g.strokeText('D'+(i+1),p[0],p[1]);g.fillText('D'+(i+1),p[0],p[1]);}}
  const p=toS(0,-WORLD.wallRadius+12);if(Math.hypot(p[0]-half,p[1]-half)<lim-6*d){g.font='700 '+(10*d)+'px Rajdhani,system-ui,sans-serif';g.strokeText('GATE',p[0],p[1]);g.fillText('GATE',p[0],p[1]);}}
 const C=CAPTIVE;
 if(C&&C.group){const [cx,cy,ed]=edge(C.x,C.z),k=ed?.8:1;                                                         // the captive
  if(C.alive){
   if(C.under>0){const q=(now%700)/700;g.beginPath();g.arc(cx,cy,(7+q*13)*d*k,0,TAU);g.strokeStyle='rgba(255,70,60,'+((1-q)*.9).toFixed(2)+')';g.lineWidth=2.2*d;g.stroke();}
   g.beginPath();g.arc(cx,cy,6.2*d*k,0,TAU);g.fillStyle='#3ddc6a';g.fill();g.lineWidth=2*d;g.strokeStyle='#fff';g.stroke();
  }else{g.strokeStyle='#9a9a9a';g.lineWidth=2.2*d;g.beginPath();g.moveTo(cx-5*d,cy-5*d);g.lineTo(cx+5*d,cy+5*d);g.moveTo(cx+5*d,cy-5*d);g.lineTo(cx-5*d,cy+5*d);g.stroke();}
 }
 for(const m of monsters){if(!m.alive||!m.root.visible)continue;                                                // monsters: ALL red (brute = big, stalker = small; a green ring = going for the captive)
  const [px,py,ed]=edge(m.root.position.x,m.root.position.z),rad=(m.type==='boss'?9:m.type==='brute'?5.2:m.type==='spitter'?4.5:3.9)*d*(ed?.8:1);
  g.beginPath();g.arc(px,py,rad,0,TAU);g.fillStyle='#ff1f1f';g.fill();g.lineWidth=1.5*d;g.strokeStyle='rgba(255,255,255,.92)';g.stroke();
  if(m.target==='woman'&&C&&C.alive){g.beginPath();g.arc(px,py,rad+2.2*d,0,TAU);g.strokeStyle='rgba(80,230,120,.95)';g.lineWidth=1.3*d;g.stroke();}
 }
 g.save();g.translate(half,half);                                                                                // you: always in the centre, always pointing up
 g.beginPath();g.moveTo(0,0);g.arc(0,0,38*d,-Math.PI/2-.55,-Math.PI/2+.55);g.closePath();g.fillStyle='rgba(240,196,110,.24)';g.fill();
 g.beginPath();g.moveTo(0,-9*d);g.lineTo(6.4*d,7*d);g.lineTo(0,3.6*d);g.lineTo(-6.4*d,7*d);g.closePath();g.fillStyle='#f6d38e';g.fill();g.lineWidth=1.7*d;g.strokeStyle='#1a1208';g.stroke();
 g.restore();
 {const rN=Rv-10*d,nx=half+sn*rN,ny=half-cs*rN;                                                                  // compass: N = the gate side (-Z)
  g.beginPath();g.arc(nx,ny,7.5*d,0,TAU);g.fillStyle='rgba(12,14,20,.82)';g.fill();g.lineWidth=1.2*d;g.strokeStyle='#f0c577';g.stroke();
  g.fillStyle='#f6d38e';g.font='800 '+(10*d)+'px Rajdhani,system-ui,sans-serif';g.fillText('N',nx,ny+.5*d);}
 g.restore();
}
// PERF: adaptive resolution. If the measured FPS stays low (late waves), the render resolution is lowered step by step (never below 60% of the chosen
// quality) and raised again when there is headroom. Tweak live: AR.on=false  AR.lo=48  AR.hi=57  AR.min=.6
const AR={on:true,base:1,cur:1,min:.6,lo:48,hi:57,acc:0,n:0,last:0,warm:0};
function adaptRes(){
 const now=performance.now(),d=(now-AR.last)/1000;AR.last=now;
 if(!AR.on||!renderer||!running||!mouse.locked||d>.25||d<=0){AR.acc=0;AR.n=0;return;}
 AR.acc+=d;AR.n++;if(AR.acc<1.5)return;
 const fps=AR.n/AR.acc;AR.acc=0;AR.n=0;
 let next=AR.cur;
 if(fps<AR.lo&&AR.cur>AR.base*AR.min+.001)next=Math.max(AR.base*AR.min,AR.cur-.1);
 else if(fps>AR.hi&&AR.cur<AR.base-.001)next=Math.min(AR.base,AR.cur+.05);
 if(Math.abs(next-AR.cur)>.001){AR.cur=next;renderer.setPixelRatio(next);}
}
function frame(){requestAnimationFrame(frame);if(GFX.fps){const _n=performance.now();if(_n-GFXT.last<1000/GFX.fps-2)return;GFXT.last=_n;}const dt=Math.min(.033,clock.getDelta());if(window.__ninja&&window.__ninja.freeze)return;try{minimapUpdate(dt);}catch(e){if(!MM.err){MM.err=1;console.error('[minimap]',e);}}try{sfxUpdate(dt);}catch(e){}if(running&&mouse.locked){elapsed+=dt;updateMovement(dt);updateHooks(dt);updateBow(dt);updateMonsters(dt);updateArrows(dt);if(player.sliding){dustSpawnTimer+=dt;if(dustSpawnTimer>=.08){dustSpawnTimer=0;spawnDust();}}else dustSpawnTimer=0;updateEffects(dt);updateFps(dt);}else{dustSpawnTimer=0;if(playerMesh&&camera){syncPlayerVisuals(dt);updateHooks(0);updateBow(0);}}
 if(renderer&&scene&&camera){try{adaptRes();}catch(e){}try{gfxShadowFollow();}catch(e){}slamSafe(slamRenderPre);renderer.render(scene,camera);slamSafe(slamRenderPost);}}
function applyGraphicsQuality(showMessage=false){if(!renderer)return;gfxApplyPreset(quality);gfxApplyAll();gfxSyncUI();}

// ===================== NIGHT LOOK: moonlit street, starry sky, lit windows and lanterns =====================
// Tweak live from the console, then call nightApply(), e.g.  NIGHT.moonLight=2; NIGHT.hemi=1.2; NIGHT.exposure=1.3; nightApply()
const NIGHT={fog:0x24365f,fogDensity:.0019,exposure:1.3,hemiSky:0x6f86cc,hemiGround:0x3d4262,hemi:1.7,moonColor:0xb4c4ff,moonLight:1.7,fill:.95,lamps:true,
 moon:new THREE.Vector3(.477,.375,-.795).normalize(),windowWarm:2.6,windowBlue:1.9,lantern:3.2,lights:null};
function nightApply(){
 if(scene&&scene.fog){scene.fog.color.setHex(NIGHT.fog);scene.fog.density=NIGHT.fogDensity*(GFX.fogM||1);}
 if(renderer)renderer.toneMappingExposure=NIGHT.exposure*(GFX.bright/100);
 if(NIGHT.lights){const L=NIGHT.lights;L.hemi.color.setHex(NIGHT.hemiSky);L.hemi.groundColor.setHex(NIGHT.hemiGround);L.hemi.intensity=NIGHT.hemi;L.sun.color.setHex(NIGHT.moonColor);L.sun.intensity=NIGHT.moonLight;}
 const w=(m,col,i)=>{if(!m)return;m.emissive.setHex(col);m.emissiveIntensity=i;m.needsUpdate=true;};
 w(mats.windowWarm,0xffa83c,NIGHT.windowWarm);w(mats.windowBlue,0xffc261,NIGHT.windowBlue);w(mats.window,0xffb454,NIGHT.windowBlue*.9);w(mats.windowGreen,0xffd884,NIGHT.windowBlue*.85);   // every window pane is lit
 if(NIGHT.lights&&NIGHT.lights.fill)NIGHT.lights.fill.intensity=NIGHT.fill;

 if(mats.lanternGlow)mats.lanternGlow.emissiveIntensity=NIGHT.lantern;
}
function nightSkyTexture(){
 const W=4096,H=2048,c=document.createElement('canvas');c.width=W;c.height=H;const g=c.getContext('2d');
 const rnd=(()=>{let s=1337;return()=>((s=(s*1664525+1013904223)>>>0)/4294967296);})();
 const gr=g.createLinearGradient(0,0,0,H);   // y: 0 = zenith, H/2 = horizon, H = nadir
 gr.addColorStop(0,'#050a1e');gr.addColorStop(.25,'#0b1636');gr.addColorStop(.39,'#16264d');gr.addColorStop(.46,'#233660');gr.addColorStop(.499,'#2b3f6c');gr.addColorStop(.5,'#101a36');gr.addColorStop(1,'#0b1226');
 g.fillStyle=gr;g.fillRect(0,0,W,H);
 const m=NIGHT.moon,el=Math.asin(m.y),az=Math.atan2(m.z,m.x),mx=(az/(Math.PI*2)+.5)*W,my=(.5-el/Math.PI)*H,sx=1/Math.cos(el);
 const toPix=(a,e)=>[(a/(Math.PI*2)+.5)*W,(.5-e/Math.PI)*H];
 // stars
 for(let i=0;i<2600;i++){const e=Math.asin(.04+.96*rnd()),a=(rnd()-.5)*Math.PI*2,[x,y]=toPix(a,e),s=.6+rnd()*rnd()*1.8,wd=Math.min(6,s/Math.cos(e));
  g.globalAlpha=.25+rnd()*.65;g.fillStyle=rnd()<.25?'#bcd0ff':rnd()<.2?'#ffe8c4':'#ffffff';g.fillRect(x-wd/2,y-s/2,wd,s);}
 g.globalAlpha=1;
 // clouds: dark, soft wisps, a little lit near the moon
 for(let i=0;i<170;i++){const e=(6+rnd()*50)*Math.PI/180,a=(rnd()-.5)*Math.PI*2,[x,y]=toPix(a,e),rw=(50+rnd()*150)/Math.cos(e)*.8,rh=12+rnd()*28;
  const da=Math.abs(Math.atan2(Math.sin(a-az),Math.cos(a-az))),near=Math.max(0,1-Math.hypot(da,e-el)/.7);
  g.save();g.translate(x,y);g.scale(rw,rh);const cg=g.createRadialGradient(0,0,0,0,0,1);
  cg.addColorStop(0,near>0?`rgba(${70+near*70|0},${90+near*70|0},${140+near*60|0},${.22+.18*near})`:'rgba(28,42,80,.4)');cg.addColorStop(1,'rgba(28,42,80,0)');
  g.fillStyle=cg;g.beginPath();g.arc(0,0,1,0,7);g.fill();g.restore();}
 // moon glow + disc
 g.save();g.translate(mx,my);g.scale(sx,1);
 let hg=g.createRadialGradient(0,0,10,0,0,300);hg.addColorStop(0,'rgba(140,168,230,.26)');hg.addColorStop(.35,'rgba(105,135,205,.10)');hg.addColorStop(1,'rgba(90,120,200,0)');g.fillStyle=hg;g.beginPath();g.arc(0,0,300,0,7);g.fill();
 g.restore();
 const t=new THREE.CanvasTexture(c);t.mapping=THREE.EquirectangularReflectionMapping;t.colorSpace=THREE.SRGBColorSpace;t.minFilter=THREE.LinearFilter;t.generateMipmaps=false;t.needsUpdate=true;return t;
}

function nightLamps(){   // many more light sources: wall lamps all around the big wall and lamps beside every building (instanced glow blocks + warm light pools on the ground)
 const pts=[];
 const R=WORLD.wallRadius-7,n=Math.round(Math.PI*2*R/9);for(let i=0;i<n;i++){const a=i/n*Math.PI*2;pts.push([Math.cos(a)*R,4.2,Math.sin(a)*R]);}
 for(const c of colliders){if(c.kind!=='building'||c.bottom||c.top<5||c.halfX<3||c.halfZ<3)continue;
  for(const [dx,dz] of [[c.halfX+.35,0],[-c.halfX-.35,0],[0,c.halfZ+.35],[0,-c.halfZ-.35]])pts.push([c.x+dx,3.3,c.z+dz]);}
 if(!pts.length)return;
 const glow=new THREE.InstancedMesh(new THREE.BoxGeometry(.5,.5,.5),mats.lanternGlow,pts.length);
 const cv=document.createElement('canvas');cv.width=cv.height=64;const g=cv.getContext('2d'),gr=g.createRadialGradient(32,32,2,32,32,32);gr.addColorStop(0,'rgba(255,184,104,.62)');gr.addColorStop(.5,'rgba(255,155,72,.26)');gr.addColorStop(1,'rgba(255,145,56,0)');g.fillStyle=gr;g.fillRect(0,0,64,64);
 const tx=new THREE.CanvasTexture(cv);tx.colorSpace=THREE.SRGBColorSpace;
 const pool=new THREE.InstancedMesh(new THREE.PlaneGeometry(10,10),new THREE.MeshBasicMaterial({map:tx,transparent:true,opacity:.9,depthWrite:false,toneMapped:false}),pts.length);
 const d=new THREE.Object3D();pts.forEach((p,i)=>{d.rotation.set(0,0,0);d.position.set(p[0],p[1],p[2]);d.updateMatrix();glow.setMatrixAt(i,d.matrix);d.rotation.set(-Math.PI/2,0,0);d.position.set(p[0],.078,p[2]);d.updateMatrix();pool.setMatrixAt(i,d.matrix);});
 for(const m of [glow,pool]){m.name='NightLamps';m.castShadow=false;m.receiveShadow=false;m.frustumCulled=false;m.instanceMatrix.setUsage(THREE.StaticDrawUsage);worldRoot.add(m);}
}

// ===================== OUTSKIRTS: ruined buildings beyond the big wall, with flames and smoke (cheap: unlit silhouettes + two point clouds) =====================
// Tweak live: OUTSK.fire.visible=false  OUTSK.smoke.visible=false  OUTSK.wind.set(2,0,.5)   (counts are set at build time: OUTSK.ruins / .fires / .fireN / .smokeN)
const OUTSK={ruins:46,fires:26,fireN:12,smokeN:16,rMin:215,rMax:430,seed:7,wind:new THREE.Vector3(1.2,0,.4),fire:null,smoke:null};
function outskPoints(n,additive,tex){
 const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.BufferAttribute(new Float32Array(n*3),3));geo.setAttribute('aSize',new THREE.BufferAttribute(new Float32Array(n),1));geo.setAttribute('aAlpha',new THREE.BufferAttribute(new Float32Array(n),1));geo.setAttribute('aCol',new THREE.BufferAttribute(new Float32Array(n*3),3));
 const mt=new THREE.ShaderMaterial({transparent:true,depthWrite:false,blending:additive?THREE.AdditiveBlending:THREE.NormalBlending,uniforms:{uMap:{value:tex},uScale:{value:500}},
  vertexShader:'attribute float aSize;attribute float aAlpha;attribute vec3 aCol;varying float vA;varying vec3 vC;uniform float uScale;void main(){vA=aAlpha;vC=aCol;vec4 mv=modelViewMatrix*vec4(position,1.);gl_PointSize=min(aSize*uScale/max(1.,-mv.z),160.);gl_Position=projectionMatrix*mv;}',
  fragmentShader:'uniform sampler2D uMap;varying float vA;varying vec3 vC;void main(){float a=texture2D(uMap,gl_PointCoord).a*vA;if(a<.004)discard;gl_FragColor=vec4(vC,a);}'});
 const p=new THREE.Points(geo,mt);p.frustumCulled=false;p.renderOrder=-3;return p;
}
function buildOutskirts(){
 let s=OUTSK.seed;const rnd=()=>((s=(s*1664525+1013904223)>>>0)/4294967296);
 // dark ground beyond the village so the ruins stand on something
 const gm=new THREE.Mesh(new THREE.RingGeometry(WORLD.groundRadius-2,700,40,1),new THREE.MeshBasicMaterial({color:0x0b1327}));gm.rotation.x=-Math.PI/2;gm.position.y=-.2;scene.add(gm);
 // ruined buildings: jagged rows of dark boxes (one InstancedMesh, flat unlit colour, so they read as silhouettes against the sky)
 const inst=[],spots=[];
 for(let i=0;i<OUTSK.ruins;i++){
  const a=rnd()*Math.PI*2,r=OUTSK.rMin+Math.pow(rnd(),.85)*(OUTSK.rMax-OUTSK.rMin),x=Math.cos(a)*r,z=Math.sin(a)*r,w=14+rnd()*30,d=12+rnd()*24,h=(r<300?40:26)+rnd()*48,ry=rnd()*Math.PI,cs=Math.cos(ry),sn=Math.sin(ry),cols=4;
  let top=null;
  for(let k=0;k<cols;k++){const cw=w/cols*.94,ch=h*(.5+.5*rnd()),ox=(k-(cols-1)/2)*w/cols,px=x+cs*ox,pz=z-sn*ox;inst.push([px,ch/2-.3,pz,cw,ch,d*(.8+.2*rnd()),0,ry]);if(!top||ch>top.ch)top={x:px,z:pz,ch,cw};}
  inst.push([x+cs*w*.3,h*.45,z-sn*w*.3,w*.16,h*.9,d*.45,(rnd()-.5)*.4,ry]);          // a leaning slab
  inst.push([x-cs*w*.1,2,z+sn*w*.1,w*.7,4+rnd()*4,d*1.15,0,ry]);                      // rubble at the foot
  if(spots.length<OUTSK.fires&&(i%2===0||rnd()<.4))spots.push({x:top.x+(rnd()-.5)*top.cw*.5,y:top.ch*(.55+.42*rnd()),z:top.z+(rnd()-.5)*4});
 }
 const im=new THREE.InstancedMesh(new THREE.BoxGeometry(1,1,1),new THREE.MeshBasicMaterial({color:0x070c19}),inst.length),o=new THREE.Object3D();
 inst.forEach((q,i)=>{o.position.set(q[0],q[1],q[2]);o.scale.set(q[3],q[4],q[5]);o.rotation.set(0,q[7],q[6]);o.updateMatrix();im.setMatrixAt(i,o.matrix);});
 im.frustumCulled=false;im.instanceMatrix.setUsage(THREE.StaticDrawUsage);scene.add(im);OUTSK.ruinMesh=im;
 // flames + smoke
 const cv=document.createElement('canvas');cv.width=cv.height=64;const g=cv.getContext('2d'),gr=g.createRadialGradient(32,32,0,32,32,32);gr.addColorStop(0,'rgba(255,255,255,1)');gr.addColorStop(.45,'rgba(255,255,255,.45)');gr.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=gr;g.fillRect(0,0,64,64);
 const tex=new THREE.CanvasTexture(cv);
 const E=spots.length,FN=OUTSK.fireN,SN=OUTSK.smokeN,fire=outskPoints(E*FN,true,tex),smoke=outskPoints(E*SN,false,tex);
 const rf=[],rs=[];for(let i=0;i<E*FN;i++)rf.push([rnd(),rnd(),rnd(),rnd(),rnd()]);for(let i=0;i<E*SN;i++)rs.push([rnd(),rnd(),rnd(),rnd(),rnd()]);
 const wind=OUTSK.wind,uni=()=>{const h=renderer.domElement.height;return h/(2*Math.tan(camera.fov*Math.PI/360));};
 fire.onBeforeRender=()=>{
  const T=performance.now()/1000,P=fire.geometry.attributes,u=uni();fire.material.uniforms.uScale.value=u;
  for(let e=0;e<E;e++){const sp=spots[e];for(let j=0;j<FN;j++){const i=e*FN+j,r=rf[i],life=.8+r[0]*.7,t=((T/life+r[1])%1),k=i*3;
   P.position.array[k]=sp.x+(r[2]-.5)*5*(1-t*.5)+wind.x*t*4;P.position.array[k+1]=sp.y+t*(7+5*r[3]);P.position.array[k+2]=sp.z+(r[4]-.5)*5*(1-t*.5)+wind.z*t*4;
   P.aSize.array[i]=(8+6*r[3])*(1-.55*t);P.aAlpha.array[i]=Math.min(1,t*7)*Math.pow(1-t,1.3)*.85;
   P.aCol.array[k]=1;P.aCol.array[k+1]=.86-.6*t;P.aCol.array[k+2]=.42-.38*t;}}
  P.position.needsUpdate=P.aSize.needsUpdate=P.aAlpha.needsUpdate=P.aCol.needsUpdate=true;};
 smoke.onBeforeRender=()=>{
  const T=performance.now()/1000,P=smoke.geometry.attributes,u=uni();smoke.material.uniforms.uScale.value=u;
  for(let e=0;e<E;e++){const sp=spots[e];for(let j=0;j<SN;j++){const i=e*SN+j,r=rs[i],life=8+r[0]*6,t=((T/life+r[1])%1),k=i*3;
   P.position.array[k]=sp.x+(r[2]-.5)*6+wind.x*t*45;P.position.array[k+1]=sp.y+3+t*(55+35*r[3]);P.position.array[k+2]=sp.z+(r[4]-.5)*6+wind.z*t*45;
   P.aSize.array[i]=10+34*t*(.7+.6*r[3]);P.aAlpha.array[i]=Math.min(1,t*9)*(1-t)*.55;
   const warm=Math.max(0,1-t*5);P.aCol.array[k]=.10+.28*warm;P.aCol.array[k+1]=.11+.12*warm;P.aCol.array[k+2]=.15+.0*warm;}}
  P.position.needsUpdate=P.aSize.needsUpdate=P.aAlpha.needsUpdate=P.aCol.needsUpdate=true;};
 scene.add(smoke);scene.add(fire);OUTSK.fire=fire;OUTSK.smoke=smoke;
}
function nightMoon(){   // round moon disc + soft halo as camera-following sprites (placed at a fixed distance in the moon direction, so they never move relative to the sky)
 const mk=(draw,size,add)=>{const c=document.createElement('canvas');c.width=c.height=256;const g=c.getContext('2d');draw(g);const t=new THREE.CanvasTexture(c);t.colorSpace=THREE.SRGBColorSpace;
  const s=new THREE.Sprite(new THREE.SpriteMaterial({map:t,transparent:true,fog:false,toneMapped:false,depthWrite:false,blending:add?THREE.AdditiveBlending:THREE.NormalBlending}));
  s.scale.set(size,size,1);s.frustumCulled=false;s.renderOrder=-5;
  s.onBeforeRender=(r,sc,cam)=>{s.position.copy(cam.position).addScaledVector(NIGHT.moon,520);s.updateMatrixWorld(true);};scene.add(s);return s;};
 const D=520;
 mk(g=>{const h=g.createRadialGradient(128,128,20,128,128,128);h.addColorStop(0,'rgba(170,195,255,.55)');h.addColorStop(.3,'rgba(120,150,225,.2)');h.addColorStop(1,'rgba(90,120,200,0)');g.fillStyle=h;g.fillRect(0,0,256,256);},D*Math.tan(11*Math.PI/180)*2,true);
 mk(g=>{const R=118,d=g.createRadialGradient(108,108,6,128,128,R);d.addColorStop(0,'#ffffff');d.addColorStop(.75,'#f1f4ff');d.addColorStop(1,'#d3ddf2');g.fillStyle=d;g.beginPath();g.arc(128,128,R,0,7);g.fill();
  g.globalAlpha=.09;g.fillStyle='#8996b4';for(const [x,y,r] of [[96,96,22],[160,80,15],[150,150,28],[88,160,17],[176,128,11],[122,62,12]]){g.beginPath();g.arc(x,y,r,0,7);g.fill();}},D*Math.tan(3.9*Math.PI/180)*2*(256/236),false);
}
function nightLook(){
 scene.background=nightSkyTexture();nightMoon();try{buildOutskirts();}catch(err){console.warn('Outskirts failed:',err);}
 if(NIGHT.lamps)nightLamps();
   // a background texture only: no sky mesh, so aiming into the sky still cannot attach
 if(mats.cobble)mats.cobble.roughness=.4;   // wet stones catch the moon / lantern glints
 nightApply();
}
async function init(){scene=new THREE.Scene();scene.background=new THREE.Color(0x16264a);scene.fog=new THREE.FogExp2(NIGHT.fog,NIGHT.fogDensity);camera=new THREE.PerspectiveCamera(78,innerWidth/innerHeight,.1,700);renderer=new THREE.WebGLRenderer({antialias:true,powerPreference:'high-performance'});renderer.setPixelRatio(Math.min(window.devicePixelRatio||1,1.12));renderer.setSize(innerWidth,innerHeight);renderer.shadowMap.enabled=false;renderer.shadowMap.type=THREE.PCFSoftShadowMap;renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=NIGHT.exposure;document.body.insertBefore(renderer.domElement,document.body.firstChild);renderer.domElement.id='gameCanvas';clock=new THREE.Clock();raycaster=new THREE.Raycaster();
 const hemi=new THREE.HemisphereLight(NIGHT.hemiSky,NIGHT.hemiGround,NIGHT.hemi);scene.add(hemi);const sun=new THREE.DirectionalLight(NIGHT.moonColor,NIGHT.moonLight);sun.position.copy(NIGHT.moon).multiplyScalar(200);NIGHT.lights={hemi,sun};sun.castShadow=false;sun.shadow.mapSize.set(1024,1024);sun.shadow.camera.left=-220;sun.shadow.camera.right=220;sun.shadow.camera.top=220;sun.shadow.camera.bottom=-220;sun.shadow.bias=-.00035;scene.add(sun);shadowLight=sun;const fill=new THREE.DirectionalLight(0x6a80c0,NIGHT.fill);fill.position.set(-110,70,100);scene.add(fill);NIGHT.lights.fill=fill;
 buildWorld();try{nightLook();}catch(err){console.warn('Night look failed:',err);}buildGrappleTargets();initDustPool();buildPlayer();buildHookVisuals();createHipLaunchers();buildBow();buildSword();slamSafe(initSlamFx);slamSafe(swordHitFxInit);slamSafe(captiveInit);buildMonsters();syncPlayerVisuals();applyGraphicsQuality();addEvents();ui.loading.classList.remove('hidden');
 try{await loadErikaPlayer();}catch(err){console.error('Could not load Erika Archer; using the procedural fallback:',err);showToast('MODEL LOAD FAILED — FALLBACK ACTIVE');}
 clock.start();ui.loading.classList.add('hidden');document.title='Attack On City';requestAnimationFrame(frame);
 if(/[?&]animdebug/.test(location.search))window.__ninja={player,keys,mouse,hooks,erikaAnim,get erika(){return erikaPlayer},get scene(){return scene},get camera(){return camera},get renderer(){return renderer},setThird(v){thirdPerson=!!v;cameraPositionInitialized=false;applyCharacterViewMode();animateErika(.12);syncPlayerVisuals(.12);},start(){startRun();mouse.locked=true;running=true;},step(dt){elapsed+=dt;updateMovement(dt);updateHooks(dt);updateEffects(dt);},render(){renderer.render(scene,camera);},fire(){fireBothHooks();},colliders,monsters,slamFx,SLAM,startGroundSlam,freeze:false};}

// ===================== GRAPHICS / DISPLAY SETTINGS =====================
// GFX holds every option of the DISPLAY and GRAPHICS tabs. Everything is applied live and saved with the other settings.
const GFX={custom:false,res:0,scale:100,fps:0,fov:78,bright:100,contrast:100,sat:100,shadows:0,aniso:4,fx:1,fog:1,adaptive:true,shake:100,fogM:1,fxM:.7};
const GFXT={last:0};
const GFX_RES=[0,1440,1080,900,720,540];            // render height in pixels, 0 = native
const GFX_FPS=[0,30,45,60,90,120,144],GFX_ANISO=[1,4,8,16],GFX_FOGM=[.6,1,1.5],GFX_FXM=[.35,.7,1],GFX_CAP=[1,1.12,1.25,1.5];
const GFX_PRESETS=[{shadows:0,aniso:1,fx:0,adaptive:true},{shadows:0,aniso:4,fx:1,adaptive:true},{shadows:1,aniso:8,fx:2,adaptive:true},{shadows:2,aniso:16,fx:2,adaptive:false}];
const GFX_SHADOW=[{size:0,ext:0},{size:1024,ext:60},{size:2048,ext:80},{size:4096,ext:100}];
function gfxApplyPreset(q){const P=GFX_PRESETS[q]||GFX_PRESETS[1];Object.assign(GFX,P);GFX.custom=false;}
function gfxMerge(o){
 const num=(k,a,b)=>{if(typeof o[k]==='number'&&o[k]>=a&&o[k]<=b)GFX[k]=o[k];};
 num('scale',50,150);num('fov',60,110);num('bright',60,140);num('contrast',80,130);num('sat',50,140);num('shake',0,150);
 if(GFX_RES.includes(o.res))GFX.res=o.res;if(GFX_FPS.includes(o.fps))GFX.fps=o.fps;if(GFX_ANISO.includes(o.aniso))GFX.aniso=o.aniso;
 if([0,1,2,3].includes(o.shadows))GFX.shadows=o.shadows;if([0,1,2].includes(o.fx))GFX.fx=o.fx;if([0,1,2].includes(o.fog))GFX.fog=o.fog;
 if(typeof o.adaptive==='boolean')GFX.adaptive=o.adaptive;if(typeof o.custom==='boolean')GFX.custom=o.custom;
}
function gfxTargetRatio(){
 const H=Math.max(1,innerHeight);let pr=GFX.res>0?GFX.res/H:Math.min(window.devicePixelRatio||1,GFX_CAP[quality]||1.12);
 return Math.min(2.5,Math.max(.3,pr*GFX.scale/100));
}
function gfxApplyResolution(){
 if(!renderer)return;const pr=gfxTargetRatio();
 AR.base=pr;AR.cur=pr;AR.acc=0;AR.n=0;AR.on=!!GFX.adaptive;
 renderer.setPixelRatio(pr);renderer.setSize(innerWidth,innerHeight);
 if(camera){camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();}
 gfxUpdateInfo();
}
function gfxApplyShadows(){
 if(!renderer||!shadowLight||!scene)return;
 const L=GFX_SHADOW[GFX.shadows]||GFX_SHADOW[0],on=GFX.shadows>0,was=renderer.shadowMap.enabled;
 renderer.shadowMap.enabled=on;renderer.shadowMap.type=GFX.shadows>=2?THREE.PCFSoftShadowMap:THREE.PCFShadowMap;shadowLight.castShadow=on;
 if(on){
  const sh=shadowLight.shadow;if(sh.map){sh.map.dispose();sh.map=null;}
  sh.mapSize.set(L.size,L.size);const c=sh.camera;c.left=-L.ext;c.right=L.ext;c.top=L.ext;c.bottom=-L.ext;c.near=1;c.far=420;c.updateProjectionMatrix();
  sh.bias=-.0004;sh.normalBias=.06;if(!shadowLight.target.parent)scene.add(shadowLight.target);sh.needsUpdate=true;
 }
 if(on!==was){   // materials were compiled with / without shadow support: rebuild them
  const seen=new Set(),touch=m=>{if(m&&m.isMaterial&&!seen.has(m)){seen.add(m);m.needsUpdate=true;}};
  scene.traverse(o=>{if(o.material){if(Array.isArray(o.material))o.material.forEach(touch);else touch(o.material);}});
  try{for(const k in mats)touch(mats[k]);}catch(e){}try{for(const k in monsterMaterials)touch(monsterMaterials[k]);}catch(e){}
 }
 renderer.shadowMap.needsUpdate=true;
}
function gfxShadowFollow(){   // the shadow box follows the player, so a small box can stay sharp
 if(!GFX.shadows||!shadowLight||!shadowLight.castShadow)return;
 const t=shadowLight.target.position;t.set(Math.round(player.pos.x),0,Math.round(player.pos.z));
 shadowLight.position.set(t.x+NIGHT.moon.x*180,NIGHT.moon.y*180,t.z+NIGHT.moon.z*180);shadowLight.target.updateMatrixWorld();
}
function gfxApplyAniso(){
 if(!renderer||!scene)return;const a=Math.min(GFX.aniso,renderer.capabilities.getMaxAnisotropy?renderer.capabilities.getMaxAnisotropy():1),seen=new Set();
 const keys=['map','normalMap','roughnessMap','emissiveMap','bumpMap','alphaMap'];
 scene.traverse(o=>{const ms=o.material?(Array.isArray(o.material)?o.material:[o.material]):[];for(const m of ms){if(!m)continue;for(const k of keys){const t=m[k];if(t&&t.isTexture&&!seen.has(t)){seen.add(t);if(t.anisotropy!==a){t.anisotropy=a;t.needsUpdate=true;}}}}});
}
function gfxApplyLook(){
 GFX.fogM=GFX_FOGM[GFX.fog]||1;GFX.fxM=GFX_FXM[GFX.fx]==null?1:GFX_FXM[GFX.fx];
 try{nightApply();}catch(e){}
 if(renderer){const cv=renderer.domElement;cv.style.filter=(GFX.contrast!==100||GFX.sat!==100)?'contrast('+GFX.contrast+'%) saturate('+GFX.sat+'%)':'';}
}
function gfxApplyAll(){gfxApplyResolution();gfxApplyShadows();gfxApplyAniso();gfxApplyLook();}
function gfxResText(h){const asp=innerWidth/Math.max(1,innerHeight);return Math.round(h*asp)+' × '+h;}
function gfxUpdateInfo(){
 const el=document.getElementById('gInfo');if(!el||!renderer)return;
 const pr=renderer.getPixelRatio();el.innerHTML='Rendering <b>'+Math.round(innerWidth*pr)+' × '+Math.round(innerHeight*pr)+'</b><br>Screen '+innerWidth+' × '+innerHeight;
}
function gfxIsFull(){return !!(document.fullscreenElement||document.webkitFullscreenElement);}
async function gfxSetFull(on){
 try{const de=document.documentElement;
  if(on&&!gfxIsFull()){await (de.requestFullscreen||de.webkitRequestFullscreen).call(de);}
  else if(!on&&gfxIsFull()){await (document.exitFullscreen||document.webkitExitFullscreen).call(document);}
 }catch(e){}
 gfxSyncUI();
}
function gfxOnResize(){gfxApplyResolution();gfxSyncUI(true);}
function gfxSyncUI(light){
 const $g=id=>document.getElementById(id);
 const set=(id,v)=>{const e=$g(id);if(e&&e.value!==String(v))e.value=v;};
 const out=(id,t)=>{const e=$g(id);if(e)e.textContent=t;};
 const rs=$g('gRes');
 if(rs){const keep=rs.value;rs.textContent='';for(const h of GFX_RES){const o=document.createElement('option');o.value=h;o.textContent=h===0?'Native ('+Math.round(innerWidth*Math.min(window.devicePixelRatio||1,GFX_CAP[quality]||1.12))+' × '+Math.round(innerHeight*Math.min(window.devicePixelRatio||1,GFX_CAP[quality]||1.12))+')':gfxResText(h)+' ('+h+'p)';rs.appendChild(o);}rs.value=GFX.res;}
 set('gScale',GFX.scale);out('gScaleV',GFX.scale+'%');
 set('gFps',GFX.fps);set('gFov',GFX.fov);out('gFovV',GFX.fov+'°');
 set('gBright',GFX.bright);out('gBrightV',GFX.bright+'%');set('gContrast',GFX.contrast);out('gContrastV',GFX.contrast+'%');set('gSat',GFX.sat);out('gSatV',GFX.sat+'%');
 set('gShadows',GFX.shadows);set('gAniso',GFX.aniso);set('gFx',GFX.fx);set('gFog',GFX.fog);set('gShake',GFX.shake);out('gShakeV',GFX.shake+'%');
 const ad=$g('gAdaptive');if(ad)ad.checked=!!GFX.adaptive;
 set('gDisplayMode',gfxIsFull()?'full':'window');
 const q=$g('quality');if(q&&q.value!==String(quality))q.value=quality;
 const fb=$g('mmFullscreen');if(fb)fb.textContent=gfxIsFull()?'⛶ EXIT FULLSCREEN':'⛶ FULLSCREEN';
 if(window.gfxQl)window.gfxQl();gfxUpdateInfo();
}
function gfxInitUI(){
 const $g=id=>document.getElementById(id);
 // [element id, GFX key, kind, what to apply, marks the preset as Custom]
 const defs=[['gRes','res','n','res',0],['gScale','scale','n','res',0],['gAdaptive','adaptive','b','res',1],['gFps','fps','n',null,0],['gFov','fov','n',null,0],
  ['gBright','bright','n','look',0],['gContrast','contrast','n','look',0],['gSat','sat','n','look',0],['gShadows','shadows','n','shadows',1],['gAniso','aniso','n','aniso',1],
  ['gFx','fx','n','look',1],['gFog','fog','n','look',1],['gShake','shake','n',null,1]];
 for(const [id,key,kind,ap,cu] of defs){
  const el=$g(id);if(!el)continue;
  el.addEventListener(kind==='b'?'change':'input',()=>{
   GFX[key]=kind==='b'?el.checked:Number(el.value);if(cu)GFX.custom=true;
   if(ap==='res')gfxApplyResolution();else if(ap==='shadows')gfxApplyShadows();else if(ap==='aniso')gfxApplyAniso();else if(ap==='look')gfxApplyLook();
   gfxSyncUI();saveSettings();
  });
 }
 const dm=$g('gDisplayMode');if(dm)dm.addEventListener('change',()=>gfxSetFull(dm.value==='full'));
 const fb=$g('mmFullscreen');if(fb)fb.addEventListener('click',()=>gfxSetFull(!gfxIsFull()));
 const rb=$g('gReset');if(rb)rb.addEventListener('click',()=>{quality=1;Object.assign(GFX,{res:0,scale:100,fps:0,fov:78,bright:100,contrast:100,sat:100,fog:1,shake:100});gfxApplyPreset(1);gfxApplyAll();gfxSyncUI();saveSettings();});
 const onFs=()=>{gfxSyncUI();setTimeout(()=>{try{gfxApplyResolution();gfxSyncUI();}catch(e){}},150);};
 document.addEventListener('fullscreenchange',onFs);document.addEventListener('webkitfullscreenchange',onFs);
}

// ===================== SETTINGS MENU + REBINDABLE KEYS =====================
// Keys are remapped at the event level: the game keeps reading its default key codes (keys.KeyW, keys.Space ...), but the key the player
// bound to an action is translated to that default code, and the default key of a re-bound action is ignored. Saved in localStorage.
const BIND_ACTIONS=[
 {id:'forward',label:'Move forward',codes:['KeyW']},{id:'left',label:'Move left',codes:['KeyA']},
 {id:'back',label:'Move back',codes:['KeyS']},{id:'right',label:'Move right',codes:['KeyD']},
 {id:'jump',label:'Jump / wall leap / cut cables',codes:['Space']},{id:'sprint',label:'Sprint',codes:['ShiftLeft','ShiftRight']},
 {id:'slide',label:'Slide',codes:['KeyC','ControlLeft','ControlRight']},{id:'cables',label:'Fire / release cables',codes:['KeyF']},
 {id:'super',label:'Super strike',codes:['KeyX']},{id:'view',label:'First / third person',codes:['KeyV']},
 {id:'sword',label:'Select sword',codes:['Digit1','Numpad1']},{id:'bow',label:'Select bow',codes:['Digit2','Numpad2']},
 {id:'block',label:'Block (guard)',codes:['KeyQ']}
];
const BIND_DEFAULT=Object.fromEntries(BIND_ACTIONS.map(a=>[a.id,a.codes[0]]));
const BIND_DISPLAY_DEFAULT={sprint:'SHIFT',slide:'C / CTRL'};
const SETTINGS_KEY='attackOnCitySettings_v1';
let bindings={...BIND_DEFAULT},bindMap={},bindBlocked={},bindListening=null,settingsFrom='main';const bindBtns={};
function rebuildBindMap(){
 bindMap={};bindBlocked={};
 for(const a of BIND_ACTIONS)bindMap[bindings[a.id]]=a.codes[0];
 for(const a of BIND_ACTIONS){if(bindings[a.id]===a.codes[0])continue;for(const c of a.codes)if(!(c in bindMap))bindBlocked[c]=true;}
}
function remapKey(code){if(code==='Escape')return code;if(code in bindMap)return bindMap[code];return bindBlocked[code]?null:code;}
function codeLabel(c){
 if(!c)return '—';if(/^Key[A-Z]$/.test(c))return c.slice(3);if(/^Digit\d$/.test(c))return c.slice(5);if(/^Numpad\d$/.test(c))return 'NUM '+c.slice(6);
 const m={Space:'SPACE',ShiftLeft:'L-SHIFT',ShiftRight:'R-SHIFT',ControlLeft:'L-CTRL',ControlRight:'R-CTRL',AltLeft:'L-ALT',AltRight:'R-ALT',ArrowUp:'↑',ArrowDown:'↓',ArrowLeft:'←',ArrowRight:'→',Enter:'ENTER',Backspace:'BACKSPACE',CapsLock:'CAPS',Tab:'TAB',Minus:'-',Equal:'=',Comma:',',Period:'.',Slash:'/',Semicolon:';',Quote:"'",Backquote:'`',BracketLeft:'[',BracketRight:']',Backslash:'\\'};
 return m[c]||c.toUpperCase();
}
function keyLabel(id){const a=BIND_ACTIONS.find(x=>x.id===id);if(!a)return '';return bindings[id]===a.codes[0]&&BIND_DISPLAY_DEFAULT[id]?BIND_DISPLAY_DEFAULT[id]:codeLabel(bindings[id]);}
function refreshKeyHints(){const h=document.getElementById('weaponHint');if(h)h.innerHTML=weapon==='bow'?'<kbd>'+keyLabel('sword')+'</kbd> SWITCH TO SWORD':'<kbd>'+keyLabel('bow')+'</kbd> SWITCH TO BOW';}
function saveSettings(){try{localStorage.setItem(SETTINGS_KEY,JSON.stringify({sens:lookSensitivity,fps:ui.fpsToggle.checked,quality,gfx:GFX,bindings}));}catch(e){}}
function loadSettings(){
 try{const raw=localStorage.getItem(SETTINGS_KEY);if(raw){const s=JSON.parse(raw);
  if(typeof s.sens==='number'&&s.sens>=.0008&&s.sens<=.004){lookSensitivity=s.sens;ui.sensitivity.value=s.sens;}
  if(typeof s.fps==='boolean'){ui.fpsToggle.checked=s.fps;ui.fps.classList.toggle('hidden',!s.fps);}
  if(s.quality===0||s.quality===1||s.quality===2||s.quality===3){quality=s.quality;ui.quality.value=s.quality;gfxApplyPreset(quality);}
  if(s.gfx&&typeof s.gfx==='object')gfxMerge(s.gfx);
  if(s.bindings){const next={...BIND_DEFAULT};let ok=true;const used=new Set();
   for(const a of BIND_ACTIONS){const c=s.bindings[a.id];if(typeof c==='string'&&c.length<24&&c!=='Escape')next[a.id]=c;if(used.has(next[a.id])&&a.id==='block'&&typeof s.bindings.block!=='string'){const alt=['KeyE','KeyR','KeyG','KeyT','KeyZ'].find(k=>!used.has(k));if(alt)next.block=alt;}   // old save already uses Q for another action: park the new Block key on a free one
    if(used.has(next[a.id]))ok=false;used.add(next[a.id]);}
   if(ok)bindings=next;}
 }}catch(e){}
 rebuildBindMap();
}
function renderBindList(){
 const list=document.getElementById('bindList');if(!list)return;list.textContent='';
 for(const a of BIND_ACTIONS){
  const row=document.createElement('div');row.className='bindrow';const lab=document.createElement('span');lab.textContent=a.label;
  const b=document.createElement('button');b.type='button';b.className='bindbtn secondary';bindBtns[a.id]=b;
  if(bindListening===a.id){b.classList.add('listening');b.textContent='PRESS A KEY…';}else b.textContent=keyLabel(a.id);
  b.addEventListener('click',()=>{bindListening=a.id;renderBindList();});
  row.append(lab,b);list.appendChild(row);
 }
 refreshKeyHints();
}
function assignBinding(id,code){
 const other=BIND_ACTIONS.find(a=>a.id!==id&&bindings[a.id]===code);
 if(other)bindings[other.id]=bindings[id];   // already used: swap the two actions
 bindings[id]=code;rebuildBindMap();saveSettings();
}
function showSettingsTab(t){
 const map={general:['setGeneral','tabGeneral'],display:['setDisplay','tabDisplay'],graphics:['setGraphics','tabGraphics'],controls:['setControls','tabControls']};
 for(const k in map){const p=document.getElementById(map[k][0]),b=document.getElementById(map[k][1]);if(p)p.classList.toggle('hidden',k!==t);if(b)b.classList.toggle('active',k===t);}
 const body=document.getElementById('gsBody');if(body)body.scrollTop=0;
 if(typeof gfxSyncUI==='function')gfxSyncUI();
 if(bindListening){bindListening=null;renderBindList();}
}
function openSettings(from){settingsFrom=from;ui.main.classList.add('hidden');ui.pause.classList.add('hidden');document.getElementById('settingsMenu').classList.remove('hidden');showSettingsTab('general');renderBindList();}
function closeSettings(){bindListening=null;document.getElementById('settingsMenu').classList.add('hidden');saveSettings();(settingsFrom==='pause'?ui.pause:ui.main).classList.remove('hidden');}
function initSettings(){
 const $s=id=>document.getElementById(id);
 loadSettings();
 initAudioSettingsUI();
 const ql=()=>{const l=$s('qualityLabel');if(l)l.textContent=GFX.custom?'CUSTOM':(['LOW','MEDIUM','HIGH','ULTRA'][quality]||'');};window.gfxQl=ql;
 $s('settingsBtn').addEventListener('click',()=>openSettings('main'));
 $s('pauseSettingsBtn').addEventListener('click',()=>openSettings('pause'));
 $s('settingsBack').addEventListener('click',closeSettings);
 $s('tabGeneral').addEventListener('click',()=>showSettingsTab('general'));
 $s('tabControls').addEventListener('click',()=>showSettingsTab('controls'));
 $s('tabDisplay').addEventListener('click',()=>showSettingsTab('display'));
 $s('tabGraphics').addEventListener('click',()=>showSettingsTab('graphics'));
 $s('bindReset').addEventListener('click',()=>{bindings={...BIND_DEFAULT};bindListening=null;rebuildBindMap();saveSettings();renderBindList();});
 // these listeners are added after the game's own ones, so lookSensitivity / quality are already updated when we save
 for(const id of ['sensitivity','quality'])$s(id).addEventListener('input',()=>{ql();saveSettings();});
 $s('fpsToggle').addEventListener('change',saveSettings);
 // key capture for re-binding, and ESC closes the settings screen (runs before the game's own key handler)
 document.addEventListener('keydown',e=>{
  if($s('settingsMenu').classList.contains('hidden'))return;
  if(bindListening){
   e.preventDefault();e.stopImmediatePropagation();
   if(e.code==='Escape'){bindListening=null;renderBindList();return;}
   if(/^F\d+$/.test(e.code)||['Tab','MetaLeft','MetaRight','ContextMenu'].includes(e.code))return;
   const id=bindListening;bindListening=null;assignBinding(id,e.code);renderBindList();return;
  }
  if(e.code==='Escape'){e.preventDefault();e.stopImmediatePropagation();closeSettings();}
 },true);
 gfxInitUI();gfxApplyAll();gfxSyncUI();ql();renderBindList();
}
function addEvents(){ui.start.addEventListener('click',startRun);if(ui.controlsBtn)ui.controlsBtn.addEventListener('click',()=>{ui.main.classList.add('hidden');ui.controls.classList.remove('hidden');});ui.controlsBack.addEventListener('click',()=>{ui.controls.classList.add('hidden');ui.main.classList.remove('hidden');});ui.controlsStart.addEventListener('click',startRun);ui.resume.addEventListener('click',resumeRun);ui.restart.addEventListener('click',()=>{resetPlayer();resumeRun();showToast('RUN RESTARTED');});ui.mainMenu.addEventListener('click',goMainMenu);
 ui.sensitivity.addEventListener('input',e=>lookSensitivity=Number(e.target.value));ui.fpsToggle.addEventListener('change',e=>ui.fps.classList.toggle('hidden',!e.target.checked));ui.quality.addEventListener('input',e=>{quality=Number(e.target.value);applyGraphicsQuality(true);});
 document.addEventListener('pointerlockchange',()=>{mouse.locked=document.pointerLockElement===renderer.domElement;if(!mouse.locked)stopAim();if(mouse.locked){ui.hint.textContent='';if(started){running=true;paused=false;ui.pause.classList.add('hidden');}}else if(started&&running){enterPause();}else if(!started){ui.hint.textContent='CLICK TO CAPTURE MOUSE';}});
 document.addEventListener('mousemove',e=>{if(!mouse.locked||!running||playerDeath.active)return;const sens=lookSensitivity*(1-.4*bow.aimW);player.yaw-=e.movementX*sens;player.pitch-=e.movementY*sens;player.pitch=THREE.MathUtils.clamp(player.pitch,-1.28,1.28);});
 document.addEventListener('keydown',e=>{const kc=remapKey(e.code);if(['Space','ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(e.code))e.preventDefault();if(kc===null)return;if(playerDeath.active){if(kc==='Escape'&&started&&running)enterPause();return;}
  if(kc==='KeyP'){if(!e.repeat)upgToggle();return;}
  if(kc==='KeyQ'){if(!e.repeat&&running&&mouse.locked)blockStart();return;}
  if(rollLocked()){if(kc==='Escape'&&started&&running)enterPause();else if(kc==='KeyW'||kc==='KeyA'||kc==='KeyS'||kc==='KeyD'||kc==='ShiftLeft'||kc==='ShiftRight')keys[kc]=true;return;}   // rolling after a big fall: no actions
  if(player.block){if(kc==='Escape'&&started&&running)enterPause();return;}   // guarding: no other action is possible
  if(!keys[kc]&&kc==='Space'){
   const ropeActive=!!grapplePull||hooks.some(h=>h.mode!=='ready');
   if(ropeActive){
    // A cable is out: Space only cuts it. Never jump, and never let the held key trigger a mantle/jump afterwards.
    detachAll(false);player.spaceLock=true;player.jumpBuffer=0;
    showToast('CABLES CUT');
   }else{player.spaceLock=false;player.jumpBuffer=.14;}
  }
  keys[kc]=true;
  if(['Space','ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(kc))e.preventDefault();
  if(kc==='Escape'&&started&&running){enterPause();}
  
  if(FIRST_PERSON_ENABLED&&kc==='KeyV'&&!e.repeat&&running&&mouse.locked){
   thirdPerson=!thirdPerson;cameraPositionInitialized=false;applyCharacterViewMode();animateErika(.12);syncPlayerVisuals(.12);
   showToast(thirdPerson?'THIRD-PERSON VIEW':'FIRST-PERSON VIEW');
  }
  if(kc==='KeyF'&&!e.repeat&&running&&mouse.locked){fireBothHooks();}
  if(kc==='KeyX'&&!e.repeat&&running&&mouse.locked){startSuperStrike();}
  if(!e.repeat&&running&&mouse.locked){if(kc==='Digit1'||kc==='Numpad1')setWeapon('sword');else if(kc==='Digit2'||kc==='Numpad2')setWeapon('bow');}
 });
 document.addEventListener('keyup',e=>{const kc=remapKey(e.code);if(kc===null)return;keys[kc]=false;if(kc==='Space')player.spaceLock=false;});
 document.addEventListener('mousedown',e=>{if(!mouse.locked||!running||playerDeath.active||player.block||rollLocked())return;if(SUPER.aim){if(e.button===0)superFire();else if(e.button===2)superCancelAim();return;}if(e.button===0){if(weapon==='sword'){if(!player.grounded&&!player.slam){if(!lungeHoldBegin())airStrikeTap();}else if(!lungeHoldBegin())triggerSwordSlash();}else{startAim();startBowDraw();}}else if(e.button===2&&weapon==='bow'&&(bow.aiming||bow.drawing))stopAim();});
 document.addEventListener('mouseup',e=>{if(e.button===0){try{lungeHoldRelease();}catch(err){console.error(err);}releaseBow();if(!bow.pendingRelease)stopAim();}else if(e.button===2)stopAim();});
 renderer.domElement.addEventListener('click',()=>{if(started&&!mouse.locked&&ui.pause.classList.contains('hidden'))renderer.domElement.requestPointerLock?.();});
 document.addEventListener('contextmenu',e=>{if(started)e.preventDefault();});
 window.addEventListener('blur',()=>{for(const k in keys)keys[k]=false;detachAll(false);stopAim();});window.addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight);try{gfxOnResize();}catch(e){}});
 initSettings();
}
// ===== BOSS procedural animation (pure math, no THREE) =====
// Each pose: P[bone]=[x,y,z] degrees, applied in model frame as d=Rx*Ry*Rz (rest-pose axes, carried by the parent chain).
// P.hip=[dx,dy,dz] hips translation in rest-model units (cm). Model frame: +Y up, +Z forward, +X = character's left.
const BossAnim=(()=>{
 const BONES=['Hips','Spine','Spine1','Spine2','Neck','Head','Jaw','LeftShoulder','RightShoulder','LeftArm','RightArm','LeftForeArm','RightForeArm','LeftHand','RightHand','LeftUpLeg','RightUpLeg','LeftLeg','RightLeg','LeftFoot','RightFoot','LeftToeBase','RightToeBase'];
 const mk=()=>{const P={hip:[0,0,0]};for(const b of BONES)P[b]=[0,0,0];return P;};
 const lerp=(a,b,k)=>a+(b-a)*k, clamp=(v,a,b)=>v<a?a:v>b?b:v;
 const sm=k=>{k=clamp(k,0,1);return k*k*(3-2*k);};
 const D=Math.PI/180;
 function mix(A,B,k,out){out=out||mk();for(const b of BONES)for(let i=0;i<3;i++)out[b][i]=lerp(A[b][i],B[b][i],k);for(let i=0;i<3;i++)out.hip[i]=lerp(A.hip[i],B.hip[i],k);return out;}
 function copy(A,out){return mix(A,A,0,out);}
 // arm helper: s=+1 left, -1 right. drop: 0=T-pose, 90=hanging, -90=straight up. swing: about model X after lowering. out: arm abduction (extra Y). bend: forearm flexion (forward). twist: forearm twist
 function arm(P,s,drop,swing,bend,yaw,twist){P[s>0?'LeftArm':'RightArm']=[swing,yaw||0,-s*drop];P[s>0?'LeftForeArm':'RightForeArm']=[twist||0,-s*bend,0];}
 // leg helper: swing forward positive (hip flexion), knee flexion positive, foot kept flat automatically unless extra given
 function leg(P,s,fwd,knee,foot,abd){const U=s>0?'LeftUpLeg':'RightUpLeg',L=s>0?'LeftLeg':'RightLeg',F=s>0?'LeftFoot':'RightFoot';P[U]=[-fwd,0,(abd||0)*s];P[L]=[knee,0,0];P[F]=[fwd-knee+(foot||0),0,-(abd||0)*s];}
 // ---------- poses ----------
 function idle(t,P){P=P||mk();const br=Math.sin(t*1.6);
  P.hip=[0,-2+br*.6,0];P.Hips=[4,0,0];P.Spine=[3+br*.8,0,0];P.Spine1=[3+br*.8,0,0];P.Spine2=[3,0,0];P.Neck=[-4,0,0];P.Head=[-3+br,Math.sin(t*.5)*5,0];
  arm(P,1,72,-6,28,0);arm(P,-1,72,-6,28,0);P.LeftArm[2]+=0;leg(P,1,10,22);leg(P,-1,10,22);return P;}
 function walk(ph,P){P=P||mk();
  const sA=Math.sin(ph), sB=Math.sin(ph+Math.PI);
  const kneeA=Math.max(0,Math.cos(ph))*50, kneeB=Math.max(0,Math.cos(ph+Math.PI))*50;   // knee lifts while swinging forward
  const bob=Math.abs(Math.cos(ph));
  P.hip=[Math.sin(ph)*2.5,-4-bob*4.5,0];
  P.Hips=[8,Math.sin(ph)*7,Math.sin(ph)*3.5];
  P.Spine=[6,-Math.sin(ph)*5,-Math.sin(ph)*2];P.Spine1=[5,-Math.sin(ph)*5,0];P.Spine2=[3,-Math.sin(ph)*4,0];
  P.Neck=[-6,Math.sin(ph)*4,0];P.Head=[-8+bob*2,Math.sin(ph)*3,0];
  leg(P,1,12+sA*34,20+kneeA,0);leg(P,-1,12+sB*34,20+kneeB,0);
  // arms swing opposite to legs; heavy knuckle-dragging look
  arm(P,1,76-Math.abs(sB)*0,-sB*30,34+Math.max(0,sB)*14,0);arm(P,-1,76,-sA*30,34+Math.max(0,sA)*14,0);
  return P;}
 // slam keyframes (windup -> smash -> hold). u in [0,1] over each segment
 function slamRaise(P){P=P||mk();P.hip=[0,-6,-6];P.Hips=[-4,0,0];P.Spine=[-12,0,0];P.Spine1=[-14,0,0];P.Spine2=[-12,0,0];P.Neck=[8,0,0];P.Head=[10,0,0];
  arm(P,1,-80,42,18,-10);arm(P,-1,-80,42,18,-10);leg(P,1,-4,24);leg(P,-1,-4,24);return P;}
 // bent-over pose solved with FK so hands touch the ground and the feet stay planted (hipY,hipZ in cm)
 function bent(P,o){P=P||mk();P.hip=[0,o.hipY,o.hipZ];P.Hips=[o.hipsP,0,0];P.Spine=[o.lean*.40,0,0];P.Spine1=[o.lean*.35,0,0];P.Spine2=[o.lean*.25,0,0];P.Neck=[o.neck,0,0];P.Head=[o.neck*.4,0,0];
  arm(P,1,o.drop,o.swing,o.bend,6);arm(P,-1,o.drop,o.swing,o.bend,6);leg(P,1,o.thigh,o.knee);leg(P,-1,o.thigh,o.knee);return P;}
 function slamSmash(P){return bent(P,{hipY:-21.9,hipZ:24.7,thigh:30,knee:50,lean:62,drop:90,swing:-105.8,bend:0,neck:-44.6,hipsP:37.5});}
 function crouch(t,P){const br=Math.sin(t*2.4);P=bent(P,{hipY:-23.5-br*.7,hipZ:17.9,thigh:34,knee:58,lean:66+br*1.2,drop:90,swing:-100.1,bend:0,neck:-27.7+br*1.5,hipsP:33.5});P.Head[1]=Math.sin(t*.7)*4;return P;}
 function roar(u,P){P=P||mk();const k=Math.sin(clamp(u,0,1)*Math.PI);
  idle(0,P);P.Spine=[3-16*k,0,0];P.Spine1=[3-14*k,0,0];P.Spine2=[3-10*k,0,0];P.Neck=[-4+18*k,0,0];P.Head=[-3+14*k,0,0];P.Jaw=[34*k,0,0];
  arm(P,1,72-52*k,-6,28-8*k,-20*k);arm(P,-1,72-52*k,-6,28-8*k,-20*k);return P;}
 function death(u,P){P=P||mk();const k=sm(u);const A=idle(0);const B=mk();
  B.hip=[0,-60,-30];B.Hips=[-55,0,0];B.Spine=[-14,0,0];B.Spine1=[-10,0,0];B.Spine2=[-8,0,0];B.Neck=[10,0,0];B.Head=[18,0,0];
  arm(B,1,40,10,40,0);arm(B,-1,40,10,40,0);leg(B,1,70,100);leg(B,-1,70,100);
  return mix(A,B,k,P);}
 return {BONES,mk,mix,copy,idle,walk,slamRaise,slamSmash,crouch,roar,death,sm,clamp,D,bent};
})();


// ===================== BOSS: WARROK (giant) =====================
// Tweak everything here.  BOSS.wave = first wave that has a boss (set 5 for the real game; 1 = quick test), BOSS.every = repeat every N waves.
// The boss is a "monster" in the monsters[] list (so sword / arrow / super / slam / dash all find it) but its brain, body and animation are all in this block.
// Cycle: walk -> raise both fists -> SMASH the ground (a long crack races forward; jump to dodge) -> bent over & stunned for BOSS.stunT seconds (only now can it be hurt) -> get up -> walk ...
const BOSS={
 wave:5,every:5,                       // first boss in wave 5, then every 5 waves
 hp:3000,hpPerAppear:.25,dmgPerAppear:.15, // each later appearance: +25% health, +15% damage (compounding)
 heightMul:6,playerH:1.78,             // boss is 6x the player's height
 walkSpeed:6.5,turn:1.7,bodyR:1.7,     // m/s, rad/s, collision radius (m)
 introT:2.6,slamRange:36,slamCool:1.2,windT:1.25,
 waveLen:48,waveWid:10,waveSpeed:26,waveDmg:70,   // the ground crack: length, width, speed (m/s), damage to a player standing on the ground
 stunT:6,recoverT:1.1,                 // seconds bent over (vulnerable) / getting back up
 leapT:2.5,leapPeak:46,leapMinR:46,leapMaxR:62,leapCrouchT:.6,   // wave-start leap over the wall: flight time (s), extra arc height (m), landing distance from the plaza centre (m), crouch before take-off (s)
 maxHitFrac:.12,                       // one hit can never take more than this share of the boss's health (the 99999 super strike included)
 name:'WARROK',
 loadStarted:false,ready:false,failed:false,want:false,doneWave:-1,count:0,m:null,st:'none',t:0,yaw:0,ph:0,stepIdx:0,cool:0,stun:0,vuln:false,
 flash:0,flinch:0,immune:0,ghost:0,stuck:0,hitPt:null,waves:[],pool:[],segGeo:null,crackMats:null,tele:null,ui:null,rigRoot:null,wrap:null,out:null,snap:null,bl:1,blT:.3,
 ghostBar:1,barShow:0,dying:0,roared:false,impacted:false,aimLocked:false,mats:[],bones:null,head:null,scaleCfg:5.34,k:.0448,numbers:[]
};
(function(){XPSYS.xp.boss=400;})();
const _bV1=new THREE.Vector3(),_bV2=new THREE.Vector3(),_bQ=new THREE.Quaternion(),_bE=new THREE.Euler(0,0,0,'XYZ');
function bossAngDiff(a,b){let d=a-b;while(d>Math.PI)d-=Math.PI*2;while(d<-Math.PI)d+=Math.PI*2;return d;}
function bossClamp(v,a,b){return v<a?a:v>b?b:v;}
function isBossWave(n){return n>=BOSS.wave&&(n-BOSS.wave)%BOSS.every===0;}
function bossShake(v){try{slamFx.shake=Math.max(slamFx.shake||0,v);}catch(e){}}
function bossDist(){return camera?camera.position.distanceTo(BOSS.m?BOSS.m.root.position:camera.position):0;}
// ---------- sound (own synth, respects the game's volume settings) ----------
function bossSound(kind,gain){
 try{
  const v=(typeof sfxVol==='function'?sfxVol():.8);if(v<=0)return;
  if(!audioCtx)audioCtx=new (window.AudioContext||window.webkitAudioContext)();if(audioCtx.state==='suspended')audioCtx.resume();
  const ac=audioCtx,now=ac.currentTime,out=ac.destination,G=(gain==null?1:gain)*v;if(G<=.003)return;
  const noise=(dur)=>{const b=ac.createBuffer(1,Math.max(1,Math.floor(ac.sampleRate*dur)),ac.sampleRate),d=b.getChannelData(0);for(let i=0;i<d.length;i++)d[i]=Math.random()*2-1;const s=ac.createBufferSource();s.buffer=b;return s;};
  const env=(g,t0,peak,att,dur)=>{g.gain.setValueAtTime(.0001,t0);g.gain.exponentialRampToValueAtTime(Math.max(.0002,peak),t0+att);g.gain.exponentialRampToValueAtTime(.0001,t0+dur);};
  if(kind==='roar'){
   const o=ac.createOscillator(),o2=ac.createOscillator(),lfo=ac.createOscillator(),lg=ac.createGain(),f=ac.createBiquadFilter(),g=ac.createGain();
   o.type='sawtooth';o2.type='square';o.frequency.setValueAtTime(70,now);o.frequency.exponentialRampToValueAtTime(120,now+.45);o.frequency.exponentialRampToValueAtTime(42,now+2.1);
   o2.frequency.setValueAtTime(35,now);o2.frequency.exponentialRampToValueAtTime(60,now+.45);o2.frequency.exponentialRampToValueAtTime(21,now+2.1);
   lfo.frequency.value=13;lg.gain.value=14;lfo.connect(lg);lg.connect(o.frequency);
   f.type='lowpass';f.frequency.setValueAtTime(500,now);f.frequency.exponentialRampToValueAtTime(1800,now+.4);f.frequency.exponentialRampToValueAtTime(220,now+2.1);f.Q.value=3;
   env(g,now,.55*G,.12,2.2);o.connect(f);o2.connect(f);f.connect(g);g.connect(out);o.start(now);o2.start(now);lfo.start(now);o.stop(now+2.3);o2.stop(now+2.3);lfo.stop(now+2.3);
   const n=noise(2),nf=ac.createBiquadFilter(),ng=ac.createGain();nf.type='bandpass';nf.frequency.setValueAtTime(700,now);nf.frequency.exponentialRampToValueAtTime(220,now+1.8);nf.Q.value=.8;env(ng,now,.22*G,.1,1.9);n.connect(nf);nf.connect(ng);ng.connect(out);n.start(now);
  }else if(kind==='step'){
   const o=ac.createOscillator(),g=ac.createGain();o.type='sine';o.frequency.setValueAtTime(78,now);o.frequency.exponentialRampToValueAtTime(28,now+.32);env(g,now,.8*G,.008,.36);o.connect(g);g.connect(out);o.start(now);o.stop(now+.4);
   const n=noise(.3),f=ac.createBiquadFilter(),ng=ac.createGain();f.type='lowpass';f.frequency.setValueAtTime(700,now);f.frequency.exponentialRampToValueAtTime(60,now+.28);env(ng,now,.45*G,.006,.3);n.connect(f);f.connect(ng);ng.connect(out);n.start(now);
  }else if(kind==='crack'){
   const n=noise(1.6),f=ac.createBiquadFilter(),ng=ac.createGain();f.type='bandpass';f.frequency.setValueAtTime(2600,now);f.frequency.exponentialRampToValueAtTime(140,now+1.5);f.Q.value=.9;env(ng,now,.5*G,.01,1.6);n.connect(f);f.connect(ng);ng.connect(out);n.start(now);
   const o=ac.createOscillator(),g=ac.createGain();o.type='sine';o.frequency.setValueAtTime(95,now);o.frequency.exponentialRampToValueAtTime(22,now+1.1);env(g,now,.95*G,.01,1.2);o.connect(g);g.connect(out);o.start(now);o.stop(now+1.3);
  }else if(kind==='clang'){
   const o=ac.createOscillator(),g=ac.createGain();o.type='triangle';o.frequency.setValueAtTime(1500,now);o.frequency.exponentialRampToValueAtTime(700,now+.18);env(g,now,.22*G,.003,.22);o.connect(g);g.connect(out);o.start(now);o.stop(now+.25);
  }else if(kind==='hurt'){
   const o=ac.createOscillator(),f=ac.createBiquadFilter(),g=ac.createGain();o.type='sawtooth';o.frequency.setValueAtTime(130,now);o.frequency.exponentialRampToValueAtTime(48,now+.5);f.type='lowpass';f.frequency.value=700;env(g,now,.5*G,.02,.55);o.connect(f);f.connect(g);g.connect(out);o.start(now);o.stop(now+.6);
  }else if(kind==='death'){
   const o=ac.createOscillator(),f=ac.createBiquadFilter(),g=ac.createGain();o.type='sawtooth';o.frequency.setValueAtTime(110,now);o.frequency.exponentialRampToValueAtTime(24,now+2.6);f.type='lowpass';f.frequency.setValueAtTime(900,now);f.frequency.exponentialRampToValueAtTime(90,now+2.6);env(g,now,.6*G,.05,2.7);o.connect(f);f.connect(g);g.connect(out);o.start(now);o.stop(now+2.8);
  }
 }catch(e){}
}
// ---------- particles: a pool of sprites (dust, sparks, debris) ----------
function bossFxInit(){
 const B=BOSS;if(B.pool.length)return;
 const c=document.createElement('canvas');c.width=c.height=64;const g=c.getContext('2d'),gr=g.createRadialGradient(32,32,0,32,32,32);
 gr.addColorStop(0,'rgba(255,255,255,1)');gr.addColorStop(.35,'rgba(255,255,255,.55)');gr.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=gr;g.fillRect(0,0,64,64);
 const tex=new THREE.CanvasTexture(c);B.fxTex=tex;
 for(let i=0;i<220;i++){
  const mat=new THREE.SpriteMaterial({map:tex,transparent:true,depthWrite:false,opacity:0,color:0xffffff});
  const s=new THREE.Sprite(mat);s.visible=false;s.frustumCulled=false;scene.add(s);
  B.pool.push({s,mat,on:false,vx:0,vy:0,vz:0,life:0,max:1,s0:1,s1:1,grav:0,drag:0,op:1});
 }
 B.poolI=0;
}
function bossEmit(x,y,z,vx,vy,vz,life,s0,s1,color,add,grav,op,drag){
 const B=BOSS;if(!B.pool.length)return;if(GFX.fxM<1&&!(add&&s1>=8)&&Math.random()>GFX.fxM)return;
 let p=null;for(let k=0;k<B.pool.length;k++){const q=B.pool[(B.poolI+k)%B.pool.length];if(!q.on){p=q;B.poolI=(B.poolI+k+1)%B.pool.length;break;}}
 if(!p){p=B.pool[B.poolI];B.poolI=(B.poolI+1)%B.pool.length;}
 p.on=true;p.s.visible=true;p.s.position.set(x,y,z);p.vx=vx;p.vy=vy;p.vz=vz;p.life=p.max=life;p.s0=s0;p.s1=s1;p.grav=grav||0;p.drag=drag||0;p.op=op==null?1:op;
 p.mat.color.setHex(color);p.mat.blending=add?THREE.AdditiveBlending:THREE.NormalBlending;p.mat.opacity=p.op;p.mat.needsUpdate=true;p.s.scale.set(s0,s0,1);
}
function bossFxUpdate(dt){
 const B=BOSS;
 for(const p of B.pool){if(!p.on)continue;p.life-=dt;if(p.life<=0){p.on=false;p.s.visible=false;continue;}
  const k=1-p.life/p.max;p.vy-=p.grav*dt;const dr=Math.max(0,1-p.drag*dt);p.vx*=dr;p.vz*=dr;if(p.drag)p.vy*=dr;
  p.s.position.x+=p.vx*dt;p.s.position.y=Math.max(.05,p.s.position.y+p.vy*dt);p.s.position.z+=p.vz*dt;
  const sz=p.s0+(p.s1-p.s0)*k;p.s.scale.set(sz,sz,1);p.mat.opacity=p.op*(1-k)*(k<.08?k/.08:1);}
}
function bossDust(x,z,n,size,up,spread){for(let i=0;i<n;i++){const a=Math.random()*6.283,r=Math.random()*spread;bossEmit(x+Math.cos(a)*r*.4,.3,z+Math.sin(a)*r*.4,Math.cos(a)*r*.7,up*(.4+Math.random()*.8),Math.sin(a)*r*.7,1.2+Math.random()*1.1,size*.5,size*(1.2+Math.random()),0x7d6c58,false,-1.2,.55,.7);}}
function bossSparks(x,y,z,n,color,speed,grav){for(let i=0;i<n;i++){const a=Math.random()*6.283,u=Math.random()*2-.4;bossEmit(x,y,z,Math.cos(a)*speed*(.3+Math.random()),speed*(.2+u*.6+Math.random()*.5),Math.sin(a)*speed*(.3+Math.random()),.35+Math.random()*.45,.28+Math.random()*.3,.04,color,true,grav==null?18:grav,1,0);}}
// ---------- HTML overlay: health bar over the boss's head, banner, floating damage numbers ----------
function bossUiBuild(){
 const B=BOSS;if(B.ui)return;
 const st=document.createElement('style');st.textContent=
 '#bossBar{position:fixed;left:0;top:0;width:340px;margin-left:-170px;pointer-events:none;z-index:9;display:none;font-family:system-ui,Segoe UI,Arial,sans-serif;text-align:center;will-change:transform}'+
 '#bossBar .bn{font-weight:800;letter-spacing:.22em;font-size:13px;color:#ffd9b0;text-shadow:0 0 8px #000,0 0 3px #000;margin-bottom:3px}'+
 '#bossBar .bt{position:relative;height:17px;border:2px solid #1c0d0a;border-radius:4px;background:#2a0f0d;box-shadow:0 0 12px rgba(0,0,0,.7),inset 0 0 6px #000;overflow:hidden}'+
 '#bossBar .bg{position:absolute;left:0;top:0;bottom:0;background:#fff;opacity:.85}'+
 '#bossBar .bf{position:absolute;left:0;top:0;bottom:0;background:linear-gradient(#ff5a3c,#b3170f)}'+
 '#bossBar .bh{position:absolute;left:0;right:0;top:0;height:42%;background:rgba(255,255,255,.22)}'+
 '#bossBar .bx{font-size:11px;font-weight:700;color:#fff;text-shadow:0 0 4px #000;margin-top:2px;letter-spacing:.08em}'+
 '#bossBar .bs{font-size:12px;font-weight:800;letter-spacing:.2em;margin-top:2px;color:#9fb6c9;text-shadow:0 0 6px #000;height:15px}'+
 '#bossBar.weak .bt{border-color:#ffd24a;box-shadow:0 0 18px #ffb300,inset 0 0 6px #000}'+
 '#bossBar.weak .bs{color:#ffd24a;animation:bossPulse .5s infinite alternate}'+
 '#bossBar.ping .bt{box-shadow:0 0 16px #7fd0ff,inset 0 0 6px #000}'+
 '@keyframes bossPulse{from{opacity:.55}to{opacity:1}}'+
 '#bossBanner{position:fixed;left:50%;top:22%;transform:translateX(-50%);z-index:9;pointer-events:none;font-family:system-ui,Segoe UI,Arial,sans-serif;font-weight:900;letter-spacing:.3em;color:#ff5a3c;font-size:34px;text-shadow:0 0 18px #ff2a00,0 0 4px #000;opacity:0;white-space:nowrap}'+
 '#bossBanner.show{animation:bossBan 3.2s ease-out forwards}'+
 '@keyframes bossBan{0%{opacity:0;transform:translateX(-50%) scale(1.6)}12%{opacity:1;transform:translateX(-50%) scale(1)}80%{opacity:1}100%{opacity:0}}'+
 '.bossNum{position:fixed;left:0;top:0;pointer-events:none;z-index:9;font-family:system-ui,Segoe UI,Arial,sans-serif;font-weight:900;font-size:22px;color:#ffd24a;text-shadow:0 0 6px #000,0 0 2px #000;transition:transform .8s cubic-bezier(.1,.7,.3,1),opacity .8s;will-change:transform}';
 document.head.appendChild(st);
 const bar=document.createElement('div');bar.id='bossBar';bar.innerHTML='<div class="bn">'+B.name+'</div><div class="bt"><div class="bg"></div><div class="bf"></div><div class="bh"></div></div><div class="bx"></div><div class="bs"></div>';
 document.body.appendChild(bar);
 const ban=document.createElement('div');ban.id='bossBanner';document.body.appendChild(ban);
 B.ui={bar,bf:bar.querySelector('.bf'),bg:bar.querySelector('.bg'),bx:bar.querySelector('.bx'),bs:bar.querySelector('.bs'),ban,shown:false,lastTxt:''};
}
function bossBanner(txt){const U=BOSS.ui;if(!U)return;U.ban.textContent=txt;U.ban.classList.remove('show');void U.ban.offsetWidth;U.ban.classList.add('show');}
function bossNumber(pos,val,color){
 const B=BOSS,U=B.ui;if(!U||!camera)return;
 _bV1.copy(pos).project(camera);if(_bV1.z>1||Math.abs(_bV1.x)>1.1||Math.abs(_bV1.y)>1.1)return;
 const x=(_bV1.x*.5+.5)*innerWidth,y=(-_bV1.y*.5+.5)*innerHeight,el=document.createElement('div');el.className='bossNum';el.textContent=String(val);if(color)el.style.color=color;
 const jx=(Math.random()-.5)*50;el.style.transform='translate('+(x+jx)+'px,'+y+'px)';el.style.opacity='1';document.body.appendChild(el);
 requestAnimationFrame(()=>requestAnimationFrame(()=>{el.style.transform='translate('+(x+jx)+'px,'+(y-70)+'px)';el.style.opacity='0';}));
 setTimeout(()=>el.remove(),900);
}
function bossBarUpdate(dt){
 const B=BOSS,U=B.ui,m=B.m;if(!U)return;
 const show=!!(m&&m.alive&&running&&!paused&&B.st!=='intro-hidden'&&B.head);
 if(!show){if(U.shown){U.bar.style.display='none';U.shown=false;}return;}
 B.head.updateWorldMatrix(true,false);B.head.getWorldPosition(_bV2);_bV2.y+=B.k*30;
 const d=camera.position.distanceTo(_bV2);_bV1.copy(_bV2).project(camera);
 if(_bV1.z>1||_bV1.z<-1||Math.abs(_bV1.x)>1.25||_bV1.y>1.25||_bV1.y<-1.05){if(U.shown){U.bar.style.display='none';U.shown=false;}return;}
 const x=(_bV1.x*.5+.5)*innerWidth,y=(-_bV1.y*.5+.5)*innerHeight,sc=bossClamp(85/Math.max(20,d),.62,1.1);
 if(!U.shown){U.bar.style.display='block';U.shown=true;}
 U.bar.style.transform='translate('+x.toFixed(1)+'px,'+(y-58*sc).toFixed(1)+'px) scale('+sc.toFixed(3)+')';
 const f=bossClamp(m.hp/m.maxHp,0,1);B.ghostBar=Math.max(f,B.ghostBar-dt*.35);if(B.ghostHold>0){B.ghostHold-=dt;B.ghostBar=Math.max(B.ghostBar,f);}
 U.bf.style.width=(f*100).toFixed(1)+'%';U.bg.style.width=(B.ghostBar*100).toFixed(1)+'%';
 const tx=Math.ceil(m.hp)+' / '+m.maxHp;if(tx!==U.lastTxt){U.bx.textContent=tx;U.lastTxt=tx;}
 const weak=B.vuln&&B.st==='crouch';U.bar.classList.toggle('weak',weak);U.bar.classList.toggle('ping',B.immune>0);
 const s=weak?('EXHAUSTED - ATTACK!  '+Math.max(0,B.stun).toFixed(1)+'s'):(B.st==='dead'?'':'INVULNERABLE');if(U.bs.textContent!==s)U.bs.textContent=s;
}
// ---------- the skinned model: load, tidy materials, remember the rest pose ----------
async function bossLoad(){
 const B=BOSS;
 try{
  const node=document.getElementById('bossFbxData');if(!node)throw new Error('boss data missing');
  const [M,LM]=await Promise.all([import('three'),import('./vendor/three/examples/jsm/loaders/FBXLoader.js')]);
  const loader=new LM.FBXLoader(new M.LoadingManager());
  const model=loader.parse(erikaB64(node.textContent.trim()),'');node.remove();
  model.position.set(0,0,0);model.quaternion.identity();model.scale.set(1,1,1);model.updateMatrixWorld(true);
  const box=new M.Box3().setFromObject(model),h=box.getSize(new M.Vector3()).y;if(!(h>1))throw new Error('boss model has no size');
  const bones={},list=[];
  model.traverse(o=>{if(o.isBone){const n=o.name.replace(/^mixamorig[:_.]?/,'');if(!bones[n])bones[n]=o;}});
  for(const n of BossAnim.BONES){const b=bones[n];if(!b)continue;const par=b.parent,wp=new THREE.Quaternion();par.getWorldQuaternion(wp);
   const e={bone:b,rest:b.quaternion.clone(),restP:b.position.clone(),wp:wp.clone(),wpi:wp.clone().invert()};list.push(e);bones[n]={e,raw:b};}
  if(!bones.Hips||!bones.Hips.e)throw new Error('boss skeleton not found');
  const rig={};for(const n of BossAnim.BONES)if(bones[n]&&bones[n].e)rig[n]=bones[n].e;
  const mk=(o)=>{const mat=new M.MeshStandardMaterial({color:0xffffff,map:o&&o.map||null,normalMap:o&&o.normalMap||null,roughness:.82,metalness:.04});
   if(mat.map){mat.map.colorSpace=M.SRGBColorSpace;mat.emissiveMap=mat.map;mat.emissive.setScalar(.2);}else{mat.color.setHex(0x6b5a4a);mat.emissive.setScalar(.06);}
   mat.side=M.DoubleSide;B.mats.push(mat);return mat;};
  model.traverse(o=>{if(o.isMesh||o.isSkinnedMesh){o.frustumCulled=false;o.castShadow=false;o.receiveShadow=false;o.material=Array.isArray(o.material)?o.material.map(mk):mk(o.material);}});
  const k=(B.heightMul*B.playerH)/h;B.k=k;B.scaleCfg=B.heightMul*B.playerH/2.0;
  const wrap=new THREE.Group();model.scale.setScalar(k);wrap.add(model);B.wrap=wrap;B.model=model;
  const root=new THREE.Group();root.add(wrap);B.rigRoot=root;B.rig=rig;B.head=rig.Head?rig.Head.bone:null;
  B.out=BossAnim.idle(0);B.snap=BossAnim.copy(B.out);
  B.ready=true;
 }catch(err){console.warn('Boss could not be loaded:',err);B.failed=true;}
}
function bossApplyPose(P){
 const B=BOSS,R=B.rig;if(!R)return;
 for(const n of BossAnim.BONES){const r=R[n];if(!r)continue;const a=P[n];const D=Math.PI/180;
  _bE.set(a[0]*D,a[1]*D,a[2]*D,'XYZ');_bQ.setFromEuler(_bE);
  r.bone.quaternion.copy(r.wpi).multiply(_bQ).multiply(r.wp).multiply(r.rest);}
 const hp=R.Hips;hp.bone.position.set(hp.restP.x+P.hip[0],hp.restP.y+P.hip[1],hp.restP.z+P.hip[2]);
}
function bossSetState(st,blend){
 const B=BOSS;B.st=st;B.t=0;B.snap=BossAnim.copy(B.out,B.snap);B.bl=0;B.blT=Math.max(.01,blend||.3);
 if(st==='windup'||st==='crouch'||st==='walk')bossClearArrows();
}
function bossClearArrows(){try{for(let i=bow.arrows.length-1;i>=0;i--){const a=bow.arrows[i];if(a.monster&&a.monster===BOSS.m){disposeArrow(a);bow.arrows.splice(i,1);}}}catch(e){}}
// ---------- spawn / reset / death ----------
function bossFindSpot(){
 for(let i=0;i<50;i++){const a=Math.random()*Math.PI*2,r=WORLD.wallRadius-16-Math.random()*8;const x=Math.cos(a)*r,z=Math.sin(a)*r;if(monsterSpotFree(x,z,3.2))return {x,z};}
 const a=Math.random()*Math.PI*2,r=WORLD.wallRadius-20;return {x:Math.cos(a)*r,z:Math.sin(a)*r};
}
function bossFindLand(){   // landing spot in the middle of the city, clearly away from the captive (she stands at 0,0)
 const B=BOSS;
 for(let i=0;i<80;i++){const a=Math.random()*Math.PI*2,r=B.leapMinR+Math.random()*(B.leapMaxR-B.leapMinR);const x=Math.cos(a)*r,z=Math.sin(a)*r;if(monsterSpotFree(x,z,6))return {x,z,a};}
 const a=Math.random()*Math.PI*2;return {x:Math.cos(a)*B.leapMaxR,z:Math.sin(a)*B.leapMaxR,a};
}
function bossSpawn(){
 const B=BOSS;if(!B.ready||B.m)return;
 bossFxInit();bossUiBuild();
 const idx=B.count++,hp=Math.round(B.hp*Math.pow(1+B.hpPerAppear,idx));B.dmgMul=Math.pow(1+B.dmgPerAppear,idx);
 const spot=bossFindLand(),root=B.rigRoot;const sr=WORLD.wallRadius+3;B.leapFrom={x:Math.cos(spot.a)*sr,y:WORLD.wallHeight,z:Math.sin(spot.a)*sr};B.leapTo={x:spot.x,z:spot.z};root.position.set(B.leapFrom.x,B.leapFrom.y,B.leapFrom.z);root.rotation.set(0,0,0);root.scale.set(1,1,1);root.visible=true;B.wrap.rotation.set(0,0,0);B.wrap.position.set(0,0,0);
 for(const mat of B.mats){mat.transparent=false;mat.opacity=1;mat.needsUpdate=true;}
 const m={type:'boss',boss:true,cfg:{scale:B.scaleCfg,hp,name:B.name},root,rig:new THREE.Group(),alive:true,dead:false,hp,maxHp:hp,phase:0,attackCooldown:9,attackAnim:0,attackSide:1,recoil:0,hitMeshes:[],bodyMeshes:[],headMeshes:[],arms:[],entry:null,climb:null,roof:null,down:null,rd:null,lastSwordSerial:0,attackSerial:0,spawn:new THREE.Vector3(spot.x,0,spot.z),deadTimer:0,target:'player'};
 B.m=m;B.want=false;B.doneWave=WAVES.n;B.yaw=Math.atan2(spot.x-B.leapFrom.x,spot.z-B.leapFrom.z);root.rotation.y=B.yaw;
 B.vuln=false;B.stun=0;B.flash=0;B.flinch=0;B.ph=0;B.stepIdx=0;B.cool=BOSS.slamCool;B.ghost=0;B.stuck=0;B.roared=false;B.ghostBar=1;B.ghostHold=0;B.dying=0;B.immune=0;
 B.out=BossAnim.idle(0);B.snap=BossAnim.copy(B.out,B.snap);bossApplyPose(B.out);
 scene.add(root);monsters.push(m);bossSetState('leap',.01);B.leapPre=true;bossLandMarker(true);
 bossBanner('BOSS  -  '+B.name);bossShake(.6);updateMonsterHUD();
}
function bossRemove(){
 const B=BOSS,m=B.m;if(!m)return;
 try{scene.remove(m.root);}catch(e){}
 const i=monsters.indexOf(m);if(i>=0)monsters.splice(i,1);
 B.m=null;B.st='none';B.vuln=false;bossLandMarker(false);if(B.ui&&B.ui.shown){B.ui.bar.style.display='none';B.ui.shown=false;}
 bossClearArrows();
}
function bossClearWaves(){const B=BOSS;for(const w of B.waves)bossWaveFree(w);B.waves.length=0;if(B.tele)B.tele.group.visible=false;}
function bossReset(){
 const B=BOSS;bossLandFxClear();bossClearWaves();bossRemove();B.want=false;B.doneWave=-1;B.count=0;
 for(const p of B.pool){p.on=false;p.s.visible=false;}
 if(B.ui){B.ui.bar.style.display='none';B.ui.shown=false;}
}
function bossDie(m,kind){
 const B=BOSS;if(B.st==='dead')return;
 m.hp=0;m.alive=false;m.dead=true;B.vuln=false;playMonsterAssetSafe();xpFullLevel();monsterKills++;
 bossSetState('dead',.25);B.dying=0;B.stun=0;
 bossSound('death',1.2);bossShake(1.4);try{slamSound('boom');}catch(e){}
 const p=m.root.position;bossDust(p.x,p.z,26,6,6,9);bossBanner('BOSS DEFEATED');
 for(const w of B.waves)w.end=true;
 updateMonsterHUD();
}
function playMonsterAssetSafe(){try{playMonsterAsset('monsterDie',BOSS.m);}catch(e){}}
// ---------- damage (called from damageMonster) ----------
function bossHitPos(kind){
 const B=BOSS,m=B.m,p=m.root.position;
 if(kind==='arrow'&&B.hitPt){const v=new THREE.Vector3().copy(B.hitPt);B.hitPt=null;return v;}
 let dx=p.x-player.pos.x,dz=p.z-player.pos.z;const l=Math.hypot(dx,dz)||1;dx/=l;dz/=l;
 const reach=bossClamp(l-3.2,1.2,2.6);
 return new THREE.Vector3(player.pos.x+dx*reach+(Math.random()-.5)*.8,player.pos.y+1.2+Math.random()*.6,player.pos.z+dz*reach+(Math.random()-.5)*.8);
}
function bossDamage(m,amount,kind,quiet){
 const B=BOSS;if(!m.alive||B.st==='dead')return;
 let a=amount;
 if(kind==='sword'&&amount<9000)a=Math.round(amount*UP.swordMul*BAL.hpMul(WAVES.n));else if(kind==='arrow')a=Math.round(amount*UP.bowMul*BAL.hpMul(WAVES.n));
 const pos=bossHitPos(kind);
 if(!B.vuln){   // armoured: sparks bounce off, no damage, no reaction
  B.immune=.4;bossSparks(pos.x,pos.y,pos.z,9,0xbfe6ff,7,14);bossEmit(pos.x,pos.y,pos.z,0,0,0,.12,1.6,2.2,0xdff4ff,true,0,.8,0);
  if(!B.clangT||B.clangT<=0){bossSound('clang',.8);B.clangT=.12;}
  return;
 }
 a=Math.max(1,Math.min(a,Math.round(m.maxHp*B.maxHitFrac)));
 if(kind==='sword'&&!quiet)sound('swordHit');
 m.hp=Math.max(0,m.hp-a);m.recoil=.2;if(!quiet)sound('monsterHurt');B.flash=1;B.flinch=Math.min(1,B.flinch+.55);B.ghostHold=.45;
 bossSparks(pos.x,pos.y,pos.z,16,0xff7a2a,9,16);bossSparks(pos.x,pos.y,pos.z,8,0xffd9a0,6,12);
 bossEmit(pos.x,pos.y,pos.z,0,0,0,.16,2.4,3.6,0xfff1d0,true,0,.9,0);
 for(let i=0;i<4;i++)bossEmit(pos.x,pos.y,pos.z,(Math.random()-.5)*4,Math.random()*3+1,(Math.random()-.5)*4,.7+Math.random()*.4,.5,1.7,0x6b0f0a,false,3,.7,.5);
 bossNumber(pos,a,a>=120?'#ff7a3a':'#ffd24a');
 if(!B.hurtT||B.hurtT<=0){bossSound('hurt',.55);B.hurtT=.35;}
 if(m.hp<=0)bossDie(m,kind);
 updateMonsterHUD();
}
// ---------- the ground crack ----------
function bossCrackMats(){
 const B=BOSS;if(B.crackMats)return B.crackMats;
 B.crackMats=[];
 for(let v=0;v<3;v++){
  const c=document.createElement('canvas');c.width=256;c.height=128;const g=c.getContext('2d');g.lineCap='round';g.lineJoin='round';
  let seed=v*77+13;const rnd=()=>{seed=(seed*16807)%2147483647;return seed/2147483647;};
  const bolt=(x0,y0,x1,y1,w,depth)=>{const pts=[[x0,y0]];const n=7+Math.floor(rnd()*4);for(let i=1;i<=n;i++){const t=i/n;pts.push([x0+(x1-x0)*t+(rnd()-.5)*16*(1-t*.4),y0+(y1-y0)*t+(rnd()-.5)*10]);}
   const draw=(lw,col,blur)=>{g.beginPath();g.moveTo(pts[0][0],pts[0][1]);for(let i=1;i<pts.length;i++)g.lineTo(pts[i][0],pts[i][1]);g.lineWidth=lw;g.strokeStyle=col;g.shadowBlur=blur;g.shadowColor='#ff6a1a';g.stroke();};
   draw(w+5,'rgba(8,5,4,.92)',0);draw(w*.55,'#ff9a45',8);
   if(depth>0&&rnd()>.15){const k=2+Math.floor(rnd()*(pts.length-3)),side=rnd()>.5?1:-1;bolt(pts[k][0],pts[k][1],pts[k][0]+side*(34+rnd()*46),pts[k][1]+(rnd()-.3)*50,w*.6,depth-1);}};
  bolt(128+(rnd()-.5)*24,-4,128+(rnd()-.5)*24,132,5,2);
  for(let i=0;i<3;i++)bolt(70+rnd()*116,-4,70+rnd()*116,132,3,1);
  const tex=new THREE.CanvasTexture(c);
  B.crackMats.push(new THREE.MeshBasicMaterial({map:tex,transparent:true,depthWrite:false,polygonOffset:true,polygonOffsetFactor:-3,polygonOffsetUnits:-3,opacity:1}));
 }
 B.segGeo=new THREE.PlaneGeometry(BOSS.waveWid,3.4);
 return B.crackMats;
}
function bossTeleBuild(){
 const B=BOSS;if(B.tele)return;
 const g=new THREE.Group(),mat=new THREE.MeshBasicMaterial({color:0xff2a10,transparent:true,opacity:.2,depthWrite:false,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2});
 const mesh=new THREE.Mesh(new THREE.PlaneGeometry(1,1),mat);mesh.rotation.x=-Math.PI/2;mesh.position.y=.06;g.add(mesh);g.visible=false;scene.add(g);B.tele={group:g,mesh,mat};
}
function bossImpact(){
 const B=BOSS,m=B.m,p=m.root.position,fx=Math.sin(B.yaw),fz=Math.cos(B.yaw);
 bossCrackMats();bossTeleBuild();
 const ox=p.x+fx*1.5,oz=p.z+fz*1.5;
 B.waves.push({ox,oz,dx:fx,dz:fz,t:0,front:0,segs:[],nseg:0,hit:false,end:false,ended:0,fade:0,blocked:false});
 const ix=p.x+fx*4.7,iz=p.z+fz*4.7;   // where the fists land
 bossSound('crack',1.2);try{slamSound('boom');}catch(e){}bossShake(1.1);
 bossDust(ix,iz,22,5.5,5,7);bossSparks(ix,.6,iz,26,0xff8a3a,12,16);bossEmit(ix,.5,iz,0,0,0,.25,6,9,0xffd9a0,true,0,.8,0);
 B.tele.group.visible=false;
}
// ---------- wave-start leap: landing marker + ground impact effect ----------
function bossLandMarker(on){
 const B=BOSS;
 if(on&&!B.land){
  const g=new THREE.Group();
  const ringM=new THREE.MeshBasicMaterial({color:0xff2a10,transparent:true,opacity:.5,depthWrite:false,side:THREE.DoubleSide,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2});
  const ring=new THREE.Mesh(new THREE.RingGeometry(.88,1,64),ringM);ring.rotation.x=-Math.PI/2;g.add(ring);
  const discM=new THREE.MeshBasicMaterial({color:0xff2a10,transparent:true,opacity:.12,depthWrite:false,side:THREE.DoubleSide,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2});
  const disc=new THREE.Mesh(new THREE.CircleGeometry(1,48),discM);disc.rotation.x=-Math.PI/2;g.add(disc);
  g.position.y=.09;g.visible=false;scene.add(g);B.land={g,ringM,discM};
 }
 if(B.land){B.land.g.visible=!!on;if(on&&B.leapTo)B.land.g.position.set(B.leapTo.x,.09,B.leapTo.z);}
}
function bossCraterTex(){
 const B=BOSS;if(B.craterTex)return B.craterTex;
 const c=document.createElement('canvas');c.width=c.height=512;const g=c.getContext('2d');g.translate(256,256);
 let seed=991;const rnd=()=>{seed=(seed*16807)%2147483647;return seed/2147483647;};
 const sc=g.createRadialGradient(0,0,10,0,0,250);sc.addColorStop(0,'rgba(12,8,6,.92)');sc.addColorStop(.35,'rgba(24,16,11,.75)');sc.addColorStop(.75,'rgba(40,30,22,.35)');sc.addColorStop(1,'rgba(40,30,22,0)');
 g.fillStyle=sc;g.beginPath();g.arc(0,0,250,0,7);g.fill();
 g.lineCap='round';g.lineJoin='round';
 const crack=(ang,len,w,depth)=>{let x=0,y=0,a=ang;const pts=[[0,0]];const n=9;for(let i=1;i<=n;i++){a+=(rnd()-.5)*.5;const l=len/n;x+=Math.cos(a)*l;y+=Math.sin(a)*l;pts.push([x,y]);
   if(depth>0&&i>2&&rnd()<.35)crack(a+(rnd()>.5?1:-1)*(.5+rnd()*.5),len*.45,w*.6,depth-1);}
  const draw=(lw,col,blur)=>{g.beginPath();g.moveTo(pts[0][0],pts[0][1]);for(let i=1;i<pts.length;i++)g.lineTo(pts[i][0],pts[i][1]);g.lineWidth=lw;g.strokeStyle=col;g.shadowBlur=blur;g.shadowColor='#ff6a1a';g.stroke();};
  draw(w+5,'rgba(8,5,4,.95)',0);draw(w*.5,'#ff9a45',10);};
 for(let i=0;i<14;i++)crack(i/14*Math.PI*2+rnd()*.3,150+rnd()*95,6+rnd()*3,2);
 const t=new THREE.CanvasTexture(c);B.craterTex=t;return t;
}
function bossLandFxAdd(o){const B=BOSS;(B.landFx||(B.landFx=[])).push(o);scene.add(o.mesh);}
function bossLandFxClear(){const B=BOSS;if(!B.landFx)return;for(const o of B.landFx){try{scene.remove(o.mesh);o.mesh.material.dispose();}catch(e){}}B.landFx.length=0;}
function bossLandImpact(x,z){
 const B=BOSS;
 const mk=(geo,color,op,add,y)=>{const mat=new THREE.MeshBasicMaterial({color,transparent:true,opacity:op,depthWrite:false,side:THREE.DoubleSide,blending:add?THREE.AdditiveBlending:THREE.NormalBlending,polygonOffset:true,polygonOffsetFactor:-3,polygonOffsetUnits:-3});
  const m=new THREE.Mesh(geo,mat);m.rotation.x=-Math.PI/2;m.position.set(x,y,z);m.renderOrder=3;return m;};
 // expanding shock rings (fire + dust)
 bossLandFxAdd({kind:'ring',mesh:mk(new THREE.RingGeometry(.9,1,72),0xffa24a,.95,true,.12),age:0,life:1.0,r0:3,r1:44,op:.95});
 bossLandFxAdd({kind:'ring',mesh:mk(new THREE.RingGeometry(.8,1,72),0xd9c4a0,.7,false,.11),age:0,life:1.5,r0:2,r1:34,op:.7});
 bossLandFxAdd({kind:'ring',mesh:mk(new THREE.RingGeometry(.93,1,72),0xffe6b0,.9,true,.13),age:0,life:.65,r0:1,r1:24,op:.9});
 // burning crater with radial cracks, stays on the ground and fades
 bossLandFxAdd({kind:'crater',mesh:mk(new THREE.PlaneGeometry(2,2),0xffffff,1,false,.08),age:0,life:9,r0:6,r1:24,op:1,tex:true});
 B.landFx[B.landFx.length-1].mesh.material.map=bossCraterTex();B.landFx[B.landFx.length-1].mesh.material.needsUpdate=true;
 // flash of light
 bossEmit(x,3,z,0,0,0,.35,16,34,0xffe2b0,true,0,.9,0);
 // dust ring + debris + sparks
 for(let i=0;i<26;i++){const a=i/26*6.283+Math.random()*.2,sp=14+Math.random()*10;bossEmit(x+Math.cos(a)*3,.6,z+Math.sin(a)*3,Math.cos(a)*sp,1.5+Math.random()*2,Math.sin(a)*sp,1.6+Math.random()*1.2,3,10+Math.random()*6,0x8a7862,false,-.5,.65,1.4);}
 for(let i=0;i<26;i++){const a=Math.random()*6.283,sp=4+Math.random()*12;bossEmit(x+Math.cos(a)*2,.5,z+Math.sin(a)*2,Math.cos(a)*sp,14+Math.random()*16,Math.sin(a)*sp,1.2+Math.random()*.9,.9,.5,0x3a2f28,false,26,1,0);}
 bossSparks(x,.6,z,40,0xff8a3a,20,18);bossSparks(x,.6,z,20,0xffd9a0,14,14);
 bossDust(x,z,26,8,7,12);
 bossSound('crack',1.4);try{slamSound('boom');}catch(e){}bossShake(1.8);
}
function bossLandFxUpdate(dt){
 const B=BOSS;if(!B.landFx||!B.landFx.length)return;
 for(let i=B.landFx.length-1;i>=0;i--){const o=B.landFx[i];o.age+=dt;const k=Math.min(1,o.age/o.life);
  if(o.kind==='ring'){const e=1-Math.pow(1-k,3),r=o.r0+(o.r1-o.r0)*e;o.mesh.scale.set(r,r,1);o.mesh.material.opacity=o.op*(1-k);}
  else{const e=1-Math.pow(1-Math.min(1,o.age/.25),3),r=o.r0+(o.r1-o.r0)*e;o.mesh.scale.set(r,r,1);const f=o.age>6?Math.max(0,1-(o.age-6)/3):1;o.mesh.material.opacity=f;}
  if(k>=1){scene.remove(o.mesh);o.mesh.material.dispose();B.landFx.splice(i,1);}}
}
function bossWaveFree(w){for(const s of w.segs){try{scene.remove(s.mesh);s.mesh.material.dispose();}catch(e){}}w.segs.length=0;}
function bossWaveUpdate(dt){
 const B=BOSS,W=B.waves;
 for(let i=W.length-1;i>=0;i--){
  const w=W[i];w.t+=dt;
  if(!w.end){
   const prev=w.front;w.front=Math.min(B.waveLen,w.front+B.waveSpeed*dt);
   // grow crack segments up to the front (stops at buildings)
   const segL=3.4;
   while(w.nseg*segL<w.front&&!w.blocked){
    const s=w.nseg*segL+segL*.5,x=w.ox+w.dx*s,z=w.oz+w.dz*s;
    if(!monsterSpotFree(x,z,.4)&&Math.hypot(x,z)<WORLD.wallRadius-6){w.blocked=true;w.end=true;bossDust(x,z,10,4,4,5);break;}
    const mats=bossCrackMats(),mesh=new THREE.Mesh(B.segGeo,mats[w.nseg%3].clone());
    mesh.quaternion.setFromEuler(new THREE.Euler(-Math.PI/2,0,0,'XYZ'));
    mesh.quaternion.premultiply(new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(0,1,0),Math.atan2(w.dx,w.dz)));
    mesh.position.set(x,.07,z);mesh.scale.x=(w.nseg%2?-1:1)*.7;mesh.renderOrder=2;
    mesh.material.opacity=0;scene.add(mesh);w.segs.push({mesh,age:0,sx:(w.nseg%2?-1:1)});w.nseg++;
    bossDust(x,z,3,3.4,3.5,4);if(Math.random()<.7)bossSparks(x,.4,z,3,0xff8a3a,6,14);
    if(Math.random()<.5)bossEmit(x+(Math.random()-.5)*B.waveWid*.7,.4,z+(Math.random()-.5)*2,(Math.random()-.5)*2,5+Math.random()*5,(Math.random()-.5)*2,.9,.45,.3,0x3a2f28,false,18,1,0);
   }
   if(w.front>=B.waveLen)w.end=true;
   // damage: the band right behind the front hurts anyone still on the ground; jumping over it is the dodge
   if(!w.hit&&!playerDeath.active&&monsterRespawnTimer<=0){
    const rx=player.pos.x-w.ox,rz=player.pos.z-w.oz,along=rx*w.dx+rz*w.dz,lat=Math.abs(-rx*w.dz+rz*w.dx);
    if(lat<B.waveWid*.5+.35&&along>-3&&along<=w.front+.6&&along>=w.front-5.5&&along<=(w.blocked?w.nseg*segL:B.waveLen)){
     const grounded=player.grounded&&player.pos.y<.75;
     if(grounded){w.hit=true;damagePlayer(B.waveDmg*(B.dmgMul||1)*BAL.dmgMul(WAVES.n),{x:w.ox,z:w.oz});player.vel.y=Math.max(player.vel.y,9);player.grounded=false;bossShake(1);
      bossSparks(player.pos.x,player.pos.y+.5,player.pos.z,16,0xff8a3a,8,14);bossDust(player.pos.x,player.pos.z,8,3,4,3);}
    }
   }
   // front effects
   if(w.front>prev&&Math.random()<.9){const s=w.front,x=w.ox+w.dx*s,z=w.oz+w.dz*s,lx=-w.dz,lz=w.dx,o=(Math.random()-.5)*B.waveWid*.8;
    bossEmit(x+lx*o,.5,z+lz*o,w.dx*3,3+Math.random()*3,w.dz*3,.8,.7,2.6,0x75634f,false,5,.6,1);
    if(Math.random()<.6)bossEmit(x+lx*o,.4,z+lz*o,(Math.random()-.5)*3,6+Math.random()*5,(Math.random()-.5)*3,.8,.3,.2,0xff9a4a,true,16,1,0);}
   // the ground shakes as the crack passes close to the player
   {const rx=player.pos.x-(w.ox+w.dx*w.front),rz=player.pos.z-(w.oz+w.dz*w.front),d=Math.hypot(rx,rz);if(d<22)bossShake(.18*(1-d/22));}
  }else{w.ended+=dt;}
  // segment animation + fade
  const fadeStart=3.6;
  for(const s of w.segs){s.age+=dt;const pop=Math.min(1,s.age/.14);s.mesh.scale.x=s.sx*(.7+.3*pop);
   let op=pop;const life=s.age;if(life>fadeStart)op*=Math.max(0,1-(life-fadeStart)/1.2);s.mesh.material.opacity=op;}
  if(w.segs.length&&w.segs[w.segs.length-1].age>fadeStart+1.3&&w.end){bossWaveFree(w);W.splice(i,1);}
  else if(!w.segs.length&&w.end&&w.ended>.2){W.splice(i,1);}
 }
}
// ---------- movement ----------
function bossSpotFree(x,z){
 if(BOSS.ghost>0)return Math.hypot(x,z)<WORLD.wallRadius-9;
 return monsterSpotFree(x,z,BOSS.bodyR);
}
function bossMove(dist,dt){
 const B=BOSS,p=B.m.root.position,fx=Math.sin(B.yaw),fz=Math.cos(B.yaw);
 if(dist<=0){B.stuck=Math.max(0,B.stuck-dt);return 0;}
 const nx=p.x+fx*dist,nz=p.z+fz*dist;
 if(bossSpotFree(nx,nz)){p.x=nx;p.z=nz;B.stuck=Math.max(0,B.stuck-dt*2);return dist;}
 if(bossSpotFree(nx,p.z)){p.x=nx;B.stuck+=dt*.5;return Math.abs(fx)*dist;}
 if(bossSpotFree(p.x,nz)){p.z=nz;B.stuck+=dt*.5;return Math.abs(fz)*dist;}
 B.stuck+=dt;if(B.stuck>1){B.ghost=2.6;B.stuck=0;}
 return 0;
}
function bossTurn(want,rate){const B=BOSS;const d=bossAngDiff(want,B.yaw);B.yaw+=bossClamp(d,-rate,rate);return d;}
// ---------- the brain ----------
function bossStep(dt){
 const B=BOSS,m=B.m,root=m.root,p=root.position;B.t+=dt;B.ghost=Math.max(0,B.ghost-dt);
 B.immune=Math.max(0,B.immune-dt);B.clangT=(B.clangT||0)-dt;B.hurtT=(B.hurtT||0)-dt;B.flinch=Math.max(0,B.flinch-dt*3.2);B.flash=Math.max(0,B.flash-dt*5);
 const pl=player.pos,dx=pl.x-p.x,dz=pl.z-p.z,dist=Math.hypot(dx,dz),want=Math.atan2(dx,dz),frozen=monsterRespawnTimer>0||playerDeath.active;
 let tele=false;
 switch(B.st){
  case 'leap':{
   B.vuln=false;const F=B.leapFrom,Tt=B.leapTo;
   if(B.leapPre){   // crouch behind the wall, then launch
    const u=bossClamp(B.t/B.leapCrouchT,0,1);root.position.set(F.x,F.y,F.z);
    if(B.t>=B.leapCrouchT){B.leapPre=false;B.t=0;bossSound('roar',1.0);bossShake(.9);bossDust(F.x,F.z,12,6,5,8);}
    break;}
   const u=bossClamp(B.t/B.leapT,0,1);
   p.x=F.x+(Tt.x-F.x)*u;p.z=F.z+(Tt.z-F.z)*u;p.y=F.y*(1-u)+4*B.leapPeak*u*(1-u);
   if(B.land){const pu=.5+.5*Math.sin(B.t*14);B.land.ringM.opacity=.35+.4*pu;B.land.discM.opacity=.05+.12*u;const rr=7.5-1.5*u;B.land.g.scale.set(rr,1,rr);}
   B.yaw=Math.atan2(Tt.x-F.x,Tt.z-F.z);
   if(u>=1){p.x=Tt.x;p.y=0;p.z=Tt.z;bossLandMarker(false);bossLandImpact(Tt.x,Tt.z);B.yaw=Math.atan2(pl.x-Tt.x,pl.z-Tt.z);bossSetState('intro',.25);}
   break;}
  case 'intro':{
   B.vuln=false;bossTurn(want,.8*dt);
   if(!B.roared&&B.t>.45){B.roared=true;bossSound('roar',1.2);bossShake(.9);bossDust(p.x,p.z,18,5,4,7);}
   if(B.roared&&B.t<2.1&&Math.random()<.25)bossShake(.3);
   if(B.t>=B.introT)bossSetState('walk',.7);
   break;}
  case 'walk':{
   B.vuln=false;const diff=bossTurn(want,B.turn*dt);B.cool-=dt;
   let sp=B.walkSpeed*bossClamp(1-Math.abs(diff)/1.3,0,1)*(dist>4?1:.35);if(frozen)sp=0;
   const moved=bossMove(sp*dt,dt);B.ph+=moved/9*Math.PI*2;
   const si=Math.floor(B.ph/Math.PI);if(si!==B.stepIdx){B.stepIdx=si;const d=bossDist(),v=bossClamp(1-d/90,0,1);
    bossSound('step',.9*v);if(d<70)bossShake(.28*v);
    const side=(si%2?1:-1),rx=Math.cos(B.yaw),rz=-Math.sin(B.yaw);bossDust(p.x+rx*side*1.2+Math.sin(B.yaw)*.8,p.z+rz*side*1.2+Math.cos(B.yaw)*.8,4,3.2,2,3);}
   if(!frozen&&B.cool<=0&&dist<B.slamRange&&Math.abs(diff)<.32){B.aimLocked=false;bossSetState('windup',.5);}
   break;}
  case 'windup':{
   B.vuln=false;if(B.t<B.windT-.45)bossTurn(want,3.2*dt);else B.aimLocked=true;
   tele=true;if(B.t>=B.windT)bossSetState('smash',.14);
   break;}
  case 'smash':{
   B.vuln=false;
   if(B.t>=.2&&!B.impacted){B.impacted=true;bossImpact();B.stun=B.stunT;B.vuln=true;bossSetState('crouch',.3);B.impacted=false;}
   break;}
  case 'crouch':{
   B.vuln=true;B.stun-=dt;
   if(B.stun<=0){B.vuln=false;bossSetState('recover',.9);}
   break;}
  case 'recover':{
   B.vuln=false;if(B.t>=B.recoverT){B.cool=B.slamCool;bossSetState('walk',.8);}
   break;}
  case 'dead':{
   B.vuln=false;B.dying+=dt;
   if(B.dying>3.6){const k=bossClamp((B.dying-3.6)/1.6,0,1);
    for(const mat of B.mats){if(!mat.transparent){mat.transparent=true;mat.needsUpdate=true;}mat.opacity=1-k;}
    if(k>=1){bossRemove();return;}}
   break;}
 }
 // telegraph strip on the ground
 if(B.tele){
  if(tele){const T=B.tele,u=bossClamp((B.t-.1)/.35,0,1),fx=Math.sin(B.yaw),fz=Math.cos(B.yaw);
   T.group.visible=true;T.group.position.set(p.x+fx*1.5,0,p.z+fz*1.5);T.group.rotation.y=Math.atan2(fx,fz);
   T.mesh.scale.set(B.waveWid,B.waveLen*u,1);T.mesh.position.z=B.waveLen*u*.5;T.mat.opacity=u*(.14+.12*Math.sin(B.t*18));}
  else if(B.st!=='windup')B.tele.group.visible=false;
 }
 // pose
 let T;const BA=BossAnim;
 switch(B.st){
  case 'leap':{
   if(B.leapPre){T=BA.crouch(B.t*.4,B.tmp1||(B.tmp1=BA.mk()));}
   else{const u=bossClamp(B.t/B.leapT,0,1);T=BA.slamRaise(B.tmp1||(B.tmp1=BA.mk()));if(u>.55){const k=BA.sm((u-.55)/.45);const S=BA.slamSmash(B.tmp2||(B.tmp2=BA.mk()));T=BA.mix(T,S,k*.8,B.tmp3||(B.tmp3=BA.mk()));}}
   break;}
  case 'intro':{const u=B.t/B.introT;T=BA.roar(bossClamp((B.t-.35)/1.9,0,1),B.tmp1||(B.tmp1=BA.mk()));if(B.t<.35){BA.idle(B.t,B.tmp2||(B.tmp2=BA.mk()));T=B.tmp2;}break;}
  case 'walk':T=BA.walk(B.ph,B.tmp1||(B.tmp1=BA.mk()));break;
  case 'windup':{T=BA.slamRaise(B.tmp1||(B.tmp1=BA.mk()));const tr=Math.sin(B.t*40)*(B.t>.5?2.2:.8);T.LeftArm[0]+=tr;T.RightArm[0]-=tr;T.Spine[0]+=tr*.5;break;}
  case 'smash':T=BA.slamSmash(B.tmp1||(B.tmp1=BA.mk()));break;
  case 'crouch':T=BA.crouch(B.t,B.tmp1||(B.tmp1=BA.mk()));break;
  case 'recover':T=BA.idle(B.t,B.tmp1||(B.tmp1=BA.mk()));break;
  case 'dead':T=BA.death(bossClamp(B.t/2.2,0,1),B.tmp1||(B.tmp1=BA.mk()));break;
  default:T=BA.idle(B.t,B.tmp1||(B.tmp1=BA.mk()));
 }
 B.bl=Math.min(1,B.bl+dt/B.blT);BA.mix(B.snap,T,BA.sm(B.bl),B.out);
 const P=B.out,f=B.flinch;
 if(f>0){P.Spine[0]-=f*9;P.Spine1[0]-=f*6;P.Neck[0]+=f*10;P.Head[0]+=f*14;P.Spine[2]+=f*Math.sin(B.t*50)*3;}
 bossApplyPose(P);
 root.rotation.y=B.yaw;
 B.wrap.rotation.x=B.st==='dead'?-BA.sm(bossClamp((B.dying-.5)/1.7,0,1))*1.35:0;
 // hit flash + a glow while exhausted (shows where to hit)
 const glow=B.vuln&&B.st==='crouch'?.1+.06*Math.sin(B.t*9):0,base=.2;
 for(const mat of B.mats){mat.emissive.setRGB(base+B.flash*.85+glow,base+B.flash*.14+glow*.35,base+B.flash*.08);}
}
function bossUpdate(dt){
 const B=BOSS;
 try{
  if(!B.loadStarted){B.loadStarted=true;bossLoad();}
  if(monsters.length&&WAVES.state==='fight'&&isBossWave(WAVES.n)&&B.doneWave!==WAVES.n&&!B.m){
   if(B.failed){B.doneWave=WAVES.n;B.want=false;}
   else{B.want=true;if(B.ready&&monsterRespawnTimer<=0&&!playerDeath.active)bossSpawn();}
  }
  if(B.m)bossStep(dt);
  if(B.pool.length){bossFxUpdate(dt);}
  bossLandFxUpdate(dt);
  if(B.waves.length)bossWaveUpdate(dt);
  bossBarUpdate(dt);
 }catch(err){if(!B.errShown){B.errShown=true;console.error('Boss update error:',err);}}
}

((f)=>document.readyState==='complete'?f():window.addEventListener('load',f))(()=>{try{init();}catch(err){console.error('Ninja Parkour initialization failed:',err);ui.main.classList.remove('hidden');ui.main.querySelector('.subtitle').textContent='The 3D engine could not start. Check your browser WebGL support and internet connection for the Three.js CDN.';}});
})();
