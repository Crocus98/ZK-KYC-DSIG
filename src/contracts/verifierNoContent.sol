// SPDX-License-Identifier: GPL-3.0
/*
    Copyright 2021 0KIMS association.

    This file is generated with [snarkJS](https://github.com/iden3/snarkjs).

    snarkJS is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    snarkJS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with snarkJS. If not, see <https://www.gnu.org/licenses/>.
*/

pragma solidity >=0.7.0 <0.9.0;

contract Groth16Verifier {
    // Scalar field size
    uint256 constant r =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // Base field size
    uint256 constant q =
        21888242871839275222246405745257275088696311157297823662689037894645226208583;

    // Verification Key data
    uint256 constant alphax =
        2736208394362734444053087867256550872196160870997327537267130939770917120445;
    uint256 constant alphay =
        2946749647680677441237099589034270091289977193909982227379719042040526335858;
    uint256 constant betax1 =
        12763350547194224049853477956187134245957318475665816415530141206059239696878;
    uint256 constant betax2 =
        19135525515739624709994182263370128721057512739016986614490130424260832132481;
    uint256 constant betay1 =
        15541788408661986546917932324153965667178760512808746358188516280108500059489;
    uint256 constant betay2 =
        2717269047183733232260254952197429841994884436106934647294266794758905537803;
    uint256 constant gammax1 =
        11559732032986387107991004021392285783925812861821192530917403151452391805634;
    uint256 constant gammax2 =
        10857046999023057135944570762232829481370756359578518086990519993285655852781;
    uint256 constant gammay1 =
        4082367875863433681332203403145435568316851327593401208105741076214120093531;
    uint256 constant gammay2 =
        8495653923123431417604973247489272438418190587263600148770280649306958101930;
    uint256 constant deltax1 =
        11572867732845317801400954916313890545879219956461816344462702554527004448731;
    uint256 constant deltax2 =
        15469223726159686792613584571612792877512834571906782763945603636734221984985;
    uint256 constant deltay1 =
        15080830601047998732168129322150222380487044384484136059078385079520432693274;
    uint256 constant deltay2 =
        10390256121510914728635183196621244201677238635064843107101554004866643169398;

    uint256 constant IC0x =
        4774177229593586207804595103019679879253551806590188755978104476732477596675;
    uint256 constant IC0y =
        18683456172209960893868822860422679650767579288604592205621237133694718807671;

    uint256 constant IC1x =
        21120380722141388837012787509727655048170489261822463154730426640360692546146;
    uint256 constant IC1y =
        13602935585203244777351933269074941365159438762041168553551642451214055085398;

    uint256 constant IC2x =
        3059903943035458203658606226302016226109389041802529430902834717628586499505;
    uint256 constant IC2y =
        14109391384889507159941069248961135128190535850866466506020547337447952675387;

    uint256 constant IC3x =
        7148627438278333496310724562714581080643534970876421069463742934807993646249;
    uint256 constant IC3y =
        5126246067047212173658208909285438027265787152352031849981509301171120488809;

    uint256 constant IC4x =
        11774257872768504247035715093425263444312585938518223902485258867070929852464;
    uint256 constant IC4y =
        13211497548486810161011107421469897383722305406346506593375230592258010886714;

    uint256 constant IC5x =
        11086614805143191247587684923939836027712950582068162853874938552371350725174;
    uint256 constant IC5y =
        3272420880814080189774943715281512986205530470442093959401011960970875701087;

    uint256 constant IC6x =
        16398403371316903790640649964038203249459968592591296899335461489134053716574;
    uint256 constant IC6y =
        15921520925438423587669853440929641145752670368801621468246047952949861701615;

    uint256 constant IC7x =
        18564472850162771224750268203885734045414321042382371575383419738941262328209;
    uint256 constant IC7y =
        16816363274647463605829034330576372147642623939794484134481856556238737617261;

    uint256 constant IC8x =
        1794219334920979456618621652914061558763107756468478950873143602789140124895;
    uint256 constant IC8y =
        18087395092374918000881379165218753891805915158116215195384340321157808215891;

    uint256 constant IC9x =
        4228270188270713417696166587376750542040819282180490403488713591111430176874;
    uint256 constant IC9y =
        16620283660345783674743474349819516236318574894340339312429306572402297671816;

    uint256 constant IC10x =
        1230111495979512105931502680186569896935836317890689179497494253850746183754;
    uint256 constant IC10y =
        8359159969231263948958082708946046957520837444320482242112362890378305737588;

    uint256 constant IC11x =
        8075217920063753612505836799098856704989530176872970968405408304787659646335;
    uint256 constant IC11y =
        6607674829428308812539320872926529237299049993619534860026893146689752423370;

    uint256 constant IC12x =
        1526446717383686118280091581317281693653960880158855186188069714067188422193;
    uint256 constant IC12y =
        20506310077823833408530272119311773376257317145950955686373917823958582119626;

    uint256 constant IC13x =
        16802377393651132837104754143257229531852009267122805163431844738564603202042;
    uint256 constant IC13y =
        19017579137422636034159751037951959978666621787000757085405716325475513975109;

    uint256 constant IC14x =
        16542963517865852686027129023023949937584801000775920374380025442363735002109;
    uint256 constant IC14y =
        1901451669617207798058061407456399073388303670529637745705860998171520942054;

    uint256 constant IC15x =
        18356547101071327537642515260649297309016458862733867843905447191251288195250;
    uint256 constant IC15y =
        1985140846463686772304016494105152282280096000460396301271802195309985437715;

    uint256 constant IC16x =
        7321236741151095627524413660029341488362904438877682342299459612866029213812;
    uint256 constant IC16y =
        6013729870008995928810738016801525244162230028043014026926826177175045056045;

    uint256 constant IC17x =
        13295581477527712261046452856132846211539859288485010321135677008569974913101;
    uint256 constant IC17y =
        11761925228948067780163855453956419258839728317481690323863060996705798749498;

    uint256 constant IC18x =
        16496912667118440210337334327161959445838943157852452975449683129613504687583;
    uint256 constant IC18y =
        11906022620698643100173848751362890502743043505117444717372226657754014764026;

    uint256 constant IC19x =
        12412193290770104077076777885306603825431248583916394506772965134432561198146;
    uint256 constant IC19y =
        7364024801138620900279034177230648489081155874893814017832366365376981271389;

    uint256 constant IC20x =
        17116739089066263817955074111598274500476395212569924739556442079389097757380;
    uint256 constant IC20y =
        16171540320423698202257338401517611667614061847716741823124992183314540878863;

    uint256 constant IC21x =
        182251209921389652593640649640366435881103432413240996744710612738472606086;
    uint256 constant IC21y =
        4682875532326948307025067953826857272289943691823837712353340804130315442848;

    uint256 constant IC22x =
        13769333351078152808119503790108609578755998866336259160208165973937332189929;
    uint256 constant IC22y =
        4723127220747345891446820507250930944154419588405823572567409775386368709144;

    uint256 constant IC23x =
        13522104508366136944330315548064517584091328017338198571917860121354963181469;
    uint256 constant IC23y =
        5102349027348109023014678845173865576291480559459070721786758239246642899005;

    uint256 constant IC24x =
        7456643518868313929052618978987295424550110880969887357345161050395264031156;
    uint256 constant IC24y =
        17635675096348419819000694402272126814486263499016059099985776711805869397567;

    uint256 constant IC25x =
        7972768541003357770130413837372595063913653637973141155534429632058302114134;
    uint256 constant IC25y =
        6462001971160771655526331961064037414769699624193913908506601489819713281922;

    uint256 constant IC26x =
        574814487783382549185662922986526595918859373416733992630594811762234296813;
    uint256 constant IC26y =
        19982634821141853012617611205120075224986089549894394129738311274452905913323;

    uint256 constant IC27x =
        12021122940843282166270234039972311192776719071663866628328574084888362131195;
    uint256 constant IC27y =
        63641608551603184177211697292405235510884848385564802296455368029020744892;

    uint256 constant IC28x =
        17663354781941097137715624932140357628404767981867564616418016354910567860880;
    uint256 constant IC28y =
        6738913470006550457811332631472025609525123966687961763967811827368853811216;

    uint256 constant IC29x =
        16239456900525137742061563848988736566451054778109705377906158620292804213044;
    uint256 constant IC29y =
        21180613628030974001206115194609559050633408876151204690848285799228649557945;

    uint256 constant IC30x =
        14524027166890257589161289233941527062483495081020293572164517122211721725229;
    uint256 constant IC30y =
        12454502445015148319536060623262881127965456963412952121658297890555674249202;

    uint256 constant IC31x =
        125348092575149509359432850178656371279756929770773393385170171943901834455;
    uint256 constant IC31y =
        14669834746574991073297138006097467424112732821610630701362785410026184661757;

    uint256 constant IC32x =
        18775484732627985717217407033865337466263939193810683707743508620570244817047;
    uint256 constant IC32y =
        10509563115525450070847014258083846623670151073849044638247601301569059491974;

    uint256 constant IC33x =
        2319307060328606504873348675932307647928276339034471685519466597808504091211;
    uint256 constant IC33y =
        16223921430534339122857831946282329477020360476048664806252151532211918459363;

    uint256 constant IC34x =
        4140028904304772949496002475138021325131508835174195658443479995765250881902;
    uint256 constant IC34y =
        2749153632535753531008240732384002507957293262849854421465371127932119706189;

    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(
        uint[2] calldata _pA,
        uint[2][2] calldata _pB,
        uint[2] calldata _pC,
        uint[34] calldata _pubSignals
    ) public view returns (bool) {
        assembly {
            function checkField(v) {
                if iszero(lt(v, r)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            // G1 function to multiply a G1 value(x,y) to value in an address
            function g1_mulAccC(pR, x, y, s) {
                let success
                let mIn := mload(0x40)
                mstore(mIn, x)
                mstore(add(mIn, 32), y)
                mstore(add(mIn, 64), s)

                success := staticcall(sub(gas(), 2000), 7, mIn, 96, mIn, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }

                mstore(add(mIn, 64), mload(pR))
                mstore(add(mIn, 96), mload(add(pR, 32)))

                success := staticcall(sub(gas(), 2000), 6, mIn, 128, pR, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            function checkPairing(pA, pB, pC, pubSignals, pMem) -> isOk {
                let _pPairing := add(pMem, pPairing)
                let _pVk := add(pMem, pVk)

                mstore(_pVk, IC0x)
                mstore(add(_pVk, 32), IC0y)

                // Compute the linear combination vk_x

                g1_mulAccC(_pVk, IC1x, IC1y, calldataload(add(pubSignals, 0)))

                g1_mulAccC(_pVk, IC2x, IC2y, calldataload(add(pubSignals, 32)))

                g1_mulAccC(_pVk, IC3x, IC3y, calldataload(add(pubSignals, 64)))

                g1_mulAccC(_pVk, IC4x, IC4y, calldataload(add(pubSignals, 96)))

                g1_mulAccC(_pVk, IC5x, IC5y, calldataload(add(pubSignals, 128)))

                g1_mulAccC(_pVk, IC6x, IC6y, calldataload(add(pubSignals, 160)))

                g1_mulAccC(_pVk, IC7x, IC7y, calldataload(add(pubSignals, 192)))

                g1_mulAccC(_pVk, IC8x, IC8y, calldataload(add(pubSignals, 224)))

                g1_mulAccC(_pVk, IC9x, IC9y, calldataload(add(pubSignals, 256)))

                g1_mulAccC(
                    _pVk,
                    IC10x,
                    IC10y,
                    calldataload(add(pubSignals, 288))
                )

                g1_mulAccC(
                    _pVk,
                    IC11x,
                    IC11y,
                    calldataload(add(pubSignals, 320))
                )

                g1_mulAccC(
                    _pVk,
                    IC12x,
                    IC12y,
                    calldataload(add(pubSignals, 352))
                )

                g1_mulAccC(
                    _pVk,
                    IC13x,
                    IC13y,
                    calldataload(add(pubSignals, 384))
                )

                g1_mulAccC(
                    _pVk,
                    IC14x,
                    IC14y,
                    calldataload(add(pubSignals, 416))
                )

                g1_mulAccC(
                    _pVk,
                    IC15x,
                    IC15y,
                    calldataload(add(pubSignals, 448))
                )

                g1_mulAccC(
                    _pVk,
                    IC16x,
                    IC16y,
                    calldataload(add(pubSignals, 480))
                )

                g1_mulAccC(
                    _pVk,
                    IC17x,
                    IC17y,
                    calldataload(add(pubSignals, 512))
                )

                g1_mulAccC(
                    _pVk,
                    IC18x,
                    IC18y,
                    calldataload(add(pubSignals, 544))
                )

                g1_mulAccC(
                    _pVk,
                    IC19x,
                    IC19y,
                    calldataload(add(pubSignals, 576))
                )

                g1_mulAccC(
                    _pVk,
                    IC20x,
                    IC20y,
                    calldataload(add(pubSignals, 608))
                )

                g1_mulAccC(
                    _pVk,
                    IC21x,
                    IC21y,
                    calldataload(add(pubSignals, 640))
                )

                g1_mulAccC(
                    _pVk,
                    IC22x,
                    IC22y,
                    calldataload(add(pubSignals, 672))
                )

                g1_mulAccC(
                    _pVk,
                    IC23x,
                    IC23y,
                    calldataload(add(pubSignals, 704))
                )

                g1_mulAccC(
                    _pVk,
                    IC24x,
                    IC24y,
                    calldataload(add(pubSignals, 736))
                )

                g1_mulAccC(
                    _pVk,
                    IC25x,
                    IC25y,
                    calldataload(add(pubSignals, 768))
                )

                g1_mulAccC(
                    _pVk,
                    IC26x,
                    IC26y,
                    calldataload(add(pubSignals, 800))
                )

                g1_mulAccC(
                    _pVk,
                    IC27x,
                    IC27y,
                    calldataload(add(pubSignals, 832))
                )

                g1_mulAccC(
                    _pVk,
                    IC28x,
                    IC28y,
                    calldataload(add(pubSignals, 864))
                )

                g1_mulAccC(
                    _pVk,
                    IC29x,
                    IC29y,
                    calldataload(add(pubSignals, 896))
                )

                g1_mulAccC(
                    _pVk,
                    IC30x,
                    IC30y,
                    calldataload(add(pubSignals, 928))
                )

                g1_mulAccC(
                    _pVk,
                    IC31x,
                    IC31y,
                    calldataload(add(pubSignals, 960))
                )

                g1_mulAccC(
                    _pVk,
                    IC32x,
                    IC32y,
                    calldataload(add(pubSignals, 992))
                )

                g1_mulAccC(
                    _pVk,
                    IC33x,
                    IC33y,
                    calldataload(add(pubSignals, 1024))
                )

                g1_mulAccC(
                    _pVk,
                    IC34x,
                    IC34y,
                    calldataload(add(pubSignals, 1056))
                )

                // -A
                mstore(_pPairing, calldataload(pA))
                mstore(
                    add(_pPairing, 32),
                    mod(sub(q, calldataload(add(pA, 32))), q)
                )

                // B
                mstore(add(_pPairing, 64), calldataload(pB))
                mstore(add(_pPairing, 96), calldataload(add(pB, 32)))
                mstore(add(_pPairing, 128), calldataload(add(pB, 64)))
                mstore(add(_pPairing, 160), calldataload(add(pB, 96)))

                // alpha1
                mstore(add(_pPairing, 192), alphax)
                mstore(add(_pPairing, 224), alphay)

                // beta2
                mstore(add(_pPairing, 256), betax1)
                mstore(add(_pPairing, 288), betax2)
                mstore(add(_pPairing, 320), betay1)
                mstore(add(_pPairing, 352), betay2)

                // vk_x
                mstore(add(_pPairing, 384), mload(add(pMem, pVk)))
                mstore(add(_pPairing, 416), mload(add(pMem, add(pVk, 32))))

                // gamma2
                mstore(add(_pPairing, 448), gammax1)
                mstore(add(_pPairing, 480), gammax2)
                mstore(add(_pPairing, 512), gammay1)
                mstore(add(_pPairing, 544), gammay2)

                // C
                mstore(add(_pPairing, 576), calldataload(pC))
                mstore(add(_pPairing, 608), calldataload(add(pC, 32)))

                // delta2
                mstore(add(_pPairing, 640), deltax1)
                mstore(add(_pPairing, 672), deltax2)
                mstore(add(_pPairing, 704), deltay1)
                mstore(add(_pPairing, 736), deltay2)

                let success := staticcall(
                    sub(gas(), 2000),
                    8,
                    _pPairing,
                    768,
                    _pPairing,
                    0x20
                )

                isOk := and(success, mload(_pPairing))
            }

            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))

            // Validate that all evaluations ∈ F

            checkField(calldataload(add(_pubSignals, 0)))

            checkField(calldataload(add(_pubSignals, 32)))

            checkField(calldataload(add(_pubSignals, 64)))

            checkField(calldataload(add(_pubSignals, 96)))

            checkField(calldataload(add(_pubSignals, 128)))

            checkField(calldataload(add(_pubSignals, 160)))

            checkField(calldataload(add(_pubSignals, 192)))

            checkField(calldataload(add(_pubSignals, 224)))

            checkField(calldataload(add(_pubSignals, 256)))

            checkField(calldataload(add(_pubSignals, 288)))

            checkField(calldataload(add(_pubSignals, 320)))

            checkField(calldataload(add(_pubSignals, 352)))

            checkField(calldataload(add(_pubSignals, 384)))

            checkField(calldataload(add(_pubSignals, 416)))

            checkField(calldataload(add(_pubSignals, 448)))

            checkField(calldataload(add(_pubSignals, 480)))

            checkField(calldataload(add(_pubSignals, 512)))

            checkField(calldataload(add(_pubSignals, 544)))

            checkField(calldataload(add(_pubSignals, 576)))

            checkField(calldataload(add(_pubSignals, 608)))

            checkField(calldataload(add(_pubSignals, 640)))

            checkField(calldataload(add(_pubSignals, 672)))

            checkField(calldataload(add(_pubSignals, 704)))

            checkField(calldataload(add(_pubSignals, 736)))

            checkField(calldataload(add(_pubSignals, 768)))

            checkField(calldataload(add(_pubSignals, 800)))

            checkField(calldataload(add(_pubSignals, 832)))

            checkField(calldataload(add(_pubSignals, 864)))

            checkField(calldataload(add(_pubSignals, 896)))

            checkField(calldataload(add(_pubSignals, 928)))

            checkField(calldataload(add(_pubSignals, 960)))

            checkField(calldataload(add(_pubSignals, 992)))

            checkField(calldataload(add(_pubSignals, 1024)))

            checkField(calldataload(add(_pubSignals, 1056)))

            // Validate all evaluations
            let isValid := checkPairing(_pA, _pB, _pC, _pubSignals, pMem)

            mstore(0, isValid)
            return(0, 0x20)
        }
    }
}
