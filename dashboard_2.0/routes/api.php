<?php
use App\Http\Controllers\AccessControllPermissionController;
use App\Http\Controllers\ActivityLogController;
use App\Http\Controllers\AdharPanLinkModule\AdharPanLinkController;
use App\Http\Controllers\AnalyticsController;
use App\Http\Controllers\B2C\B2CPoilicyListingController;
use App\Http\Controllers\BroadcastMasterController;
use App\Http\Controllers\ClaimMasterController;
use App\Http\Controllers\CorporatesController;
use App\Http\Controllers\CronSchedulerController;
use App\Http\Controllers\CtaMasterController;
use App\Http\Controllers\CustomerController\PolicyExpireController;
use App\Http\Controllers\CustomerDashboardController;
use App\Http\Controllers\CustomerDataController;
use App\Http\Controllers\DashboardApis;
use App\Http\Controllers\DelegateMasterController;
use App\Http\Controllers\DocumentConfigController;
use App\Http\Controllers\FaqController;
use App\Http\Controllers\FuelTypeController;
use App\Http\Controllers\getPdfController;
use App\Http\Controllers\LobClubListController;
use App\Http\Controllers\lobDataController;
use App\Http\Controllers\LobMasterController;
use App\Http\Controllers\LogsApiController;
use App\Http\Controllers\MasterCompanyController;
use App\Http\Controllers\MasterPolicy\PolicyStatusController;
use App\Http\Controllers\MasterSchedulerConfigController;
use App\Http\Controllers\Master\BrokerController;
use App\Http\Controllers\Master\CredentialController;
use App\Http\Controllers\Master\MaskConfiguratorController;
use App\Http\Controllers\MenuMasterController;
use App\Http\Controllers\mispReportDownloadController;
use App\Http\Controllers\MultiUserLoginController;
use App\Http\Controllers\OemMasterController;
use App\Http\Controllers\OfflineExcelUpload\ExcelKeyMasterController;
use App\Http\Controllers\PermissionAccessController;
use App\Http\Controllers\PincodeMasterController;
use App\Http\Controllers\PolicyUpdateModule\IssuedPolicyController;
use App\Http\Controllers\MasterPolicy\PolicyUploadController;
use App\Http\Controllers\PospIcMappingController;
use App\Http\Controllers\PospUtilityController;
use App\Http\Controllers\ProfileController;
use App\Http\Controllers\PullApiRapperController;
use App\Http\Controllers\QualificationMasterController;
use App\Http\Controllers\ReHitPdfController;
use App\Http\Controllers\RenewalController;
use App\Http\Controllers\ReportConfigurator\GroupingReportKeyUtilityController;
use App\Http\Controllers\RoleCodeMappingController;
use App\Http\Controllers\RolesController;
use App\Http\Controllers\SellNowController;
use App\Http\Controllers\SSOController;
use App\Http\Controllers\StageMasterController;
use App\Http\Controllers\StateMasterController;
use App\Http\Controllers\StatusMasterController;
use App\Http\Controllers\TagNameController;
use App\Http\Controllers\TemplateMasterController;
use App\Http\Controllers\ThemeMasterController;
use App\Http\Controllers\TokenController;
use App\Http\Controllers\UserControllerNew;
use App\Http\Controllers\UserDataUploadTemplateController;
use App\Http\Controllers\UserTypeController;
use App\Http\Controllers\User\CaptchaController;
use App\Http\Controllers\User\LoginController;
use App\Http\Controllers\User\UserAccessManagementController;
use App\Http\Controllers\User\UserController;
use App\Http\Controllers\User\UserCreationController;
use App\Http\Controllers\VehicleController;
use App\Http\Controllers\VideoBlogsMasterController;
use App\Http\Controllers\VisibilityReportDataController;
use App\Http\Controllers\OracleAgentMasterNonPayrollController;
use App\Http\Controllers\UserHierarchyController;

use App\Http\Controllers\ZoneMasterController;
use App\Http\Middleware\UpdateUserType;
use Illuminate\Support\Facades\Route;
use App\Http\Controllers\DashboardUserMigrationController;
use App\Http\Controllers\OfflineUploadPolicyController;
use App\Http\Controllers\MotorLobMappingController;
use App\Http\Controllers\PosOnboardingRedirectionController;
use App\Http\Controllers\PosCreationOnboardingController;
use App\Http\Controllers\UserControllerAU;
use App\Http\Controllers\CommissionController;
use App\Http\Controllers\IPPBSsoController;
use App\Http\Controllers\PaymentStatusController;
use App\Http\Controllers\BclSSO;
use App\Http\Controllers\CityMasterController;
use App\Http\Controllers\ConfigMasterExcelController;
use App\Http\Controllers\DashboardApiNew;
use App\Http\Controllers\MaskDataController;
use App\Http\Controllers\PartnerController;



Route::get('/', function () {
    return response()->json([
        'status'  => false,
        'message' => 'You do not have permission to access to this resource.',
    ]);
});

Route::post('maskData', [MaskDataController::class, 'maskData']);

Route::post('policy-details', [PolicyStatusController::class, 'getPolicyDetailsByCustomerMobile'])->middleware('basic.auth');
Route::post('paymentCommonResponce', [PaymentStatusController::class, 'paymentCommonResponce']);
 //Route for IPPB SSO
 Route::post('generate-token-ippb', [IPPBSsoController::class, 'create']);
 Route::middleware('validate.token.ippb')->group(function () {
    Route::post('sso-login-token-validate', [IPPBSsoController::class, 'loginTokenValidate']);  
    Route::post('PaymentAcknowledgement', [PaymentStatusController::class, 'PaymentAcknowledgement']);
});

Route::middleware('basic.auth')->group(function () {
    Route::group(['prefix' => 'v1'], function () {
    Route::post('sso-login-token-validate', [IPPBSsoController::class, 'loginTokenValidate']);  
    Route::post('PaymentAcknowledgement', [PaymentStatusController::class, 'PaymentAcknowledgement']);
    });
});

Route::post('validate-token', [IPPBSsoController::class, 'validateTokenIPPB'])->middleware('basic.auth');
Route::post('generate-token-api', [TokenController::class, 'generateTokenApi'])->middleware('basic.auth');

Route::post('lobWiseData', [PaymentStatusController::class, 'lobWiseData'])->middleware('basic.auth');

Route::post('encryptPayload', [PaymentStatusController::class, 'encryptPayload']);
Route::post('decryptPayload', [PaymentStatusController::class, 'decryptPayload']);
Route::post('validateTokenIndiaPost', [IPPBSsoController::class, 'validateTokenIndiaPost']);
Route::post('paymentGatewayRedirection', [PaymentStatusController::class, 'paymentGatewayRedirection']);

Route::post('encryptPayloadIPPB', [PaymentStatusController::class, 'encryptPayloadIPPB']);
Route::post('decryptPayloadIPPB', [PaymentStatusController::class, 'decryptPayloadIPPB']);

Route::post('/posupload', [PosCreationOnboardingController::class, 'PosCreationOnboarding']);
Route::post('/pospcheck', [PosCreationOnboardingController::class, 'statusChange']);
Route::post('getLandingPageData', [TokenController::class, 'getLandingPageData']);
Route::post('/user_type', [UserTypeController::class, 'show_user_type']);
Route::post('/user_details', [LoginController::class, 'ListallUserDetails']);
Route::get('/customerPolicyExpireData', [LoginController::class, 'customerPolicyExpireData']);
Route::get('/nonpayroll-agent-master-process', [OracleAgentMasterNonPayrollController::class, 'NonPayrollAgentMasterProcess']);


        //Payment Gateway Configuration
        Route::post('paymentDetails', [PaymentStatusController::class, 'paymentDetails'])->middleware('basic.auth');
        
//login
Route::middleware(['decrypt.payload', 'encrypt.response'])->group(function () {
    Route::post('/logoutAll', [LoginController::class, 'logoutAll']);


    Route::middleware(['throttle:ApiRateLimiter'])->group(function () {
        Route::get('/brokerData', [LoginController::class, 'brokerData']);
        Route::post('/login', [LoginController::class, 'customerLogin']);


        Route::post('/send-email', [LoginController::class, 'sendEmail'])->name('send-email');
        Route::post('/forget-password', [LoginController::class, 'forgetPassword'])->name('forget-password');
        Route::post('/verify-otp', [LoginController::class, 'verifyCustomerOtp']);
        Route::post('/verify-totp', [LoginController::class, 'verifyCustomerTotp']);
        Route::post('/request-qr', [LoginController::class, 'CustomerResendQrCode']);
        Route::post('/reset-password', [LoginController::class, 'SaveResetPassword']);
        Route::post('/set-new-password', [LoginController::class, 'SetNewPassword']);
    });

    Route::post('users/get_users_data', [UserController::class, 'getUsersData']);

    //report configurator

    Route::post('generate_login_token', [SSOController::class, 'create']);
    // Route::post('login_token_validate', [SSOController::class, 'TokenValidate']);
    Route::post('generate_login_token_hero_sso', [SSOController::class, 'generate']);
    Route::post('login_token_validate', [SSOController::class, 'loginTokenValidate']);
    Route::post('generate_login_token_bcl_sso', [BclSSO::class, 'generateToken']);
    Route::get('validate_login_token_bcl_sso', [BclSSO::class, 'validateToken']);
    Route::get('download_config_settings_excel', [ConfigMasterExcelController::class, 'downloadConfigSettingsExcel']);
    Route::post('upload_config_settings_excel', [ConfigMasterExcelController::class, 'uploadConfigSettingsCsv']);

    Route::group(['prefix' => 'AUUsers'], function () {
        Route::post('/generate-token', [TokenController::class, 'generateTokenApi']);
        Route::post('generate_login_token', [SSOController::class, 'create']);
        Route::post('login_to_validate_ma', [SSOController::class, 'loginToValidateAUMotor']);
        Route::post('importUserExcel', [UserControllerAU::class, 'importUserExcel']);
        Route::post('updateUserRoles', [UserControllerAU::class, 'updateUserRoles']);
        Route::post('importAUHierarchy', [UserControllerAU::class, 'importAUHierarchy']);
        Route::post('importAUBranch', [UserControllerAU::class, 'importAUBranch']);    
        Route::post('mark-user-active-inactive', [UserControllerAU::class, 'markUserActiveInactive']);    
        Route::middleware('validate.token.au')->group(function () {
            Route::post('login_to_validate', [SSOController::class, 'loginToValidateAU']); 
            Route::post('syncUsers', [UserControllerAU::class, 'store']);
            Route::post('importAUUsers', [UserControllerAU::class, 'importAUUsers']);
            Route::post('employeeSPTagging', [UserControllerAU::class, 'employeeSPTagging']);
            Route::post('syncBranch', [UserControllerAU::class, 'syncBranch']);    
            Route::post('syncDesignation', [UserControllerAU::class, 'syncDesignation']);
        });
    });

    // Protected API (requires valid token)
    Route::middleware('validate.token')->group(function () {
        Route::post('/create-users', [UserCreationController::class, 'store']);

    });

    //-------------middleware auth with sanctum
// Route::middleware('auth:sanctum')->group(function() {
Route::middleware(['auth:sanctum', UpdateUserType::class])->group(function () {
    Route::post('agentPolicyData', [PaymentStatusController::class, 'agentPolicyData']);

    Route::post('/user-hierarchy', [UserHierarchyController::class, 'show']);
    Route::post('/userHierarchyList', [UserControllerNew::class, 'userHierarchyList']);
    Route::post('activeInactiveUser', [UserControllerNew::class, 'activeInactiveUser']);

    Route::post('/generatepostoken', [PosOnboardingRedirectionController::class, 'generatePosToken']);
    
    Route::post('/userMigrationApi', [DashboardUserMigrationController::class, 'migrate']);
    Route::post('/customerMigrationApi', [DashboardUserMigrationController::class, 'migrateCustomers']);
    Route::post('/migrateEmployee', [DashboardUserMigrationController::class, 'migrateEmployee']);

    //B2C Poilicy Listing
    Route::post('/b2cPoilicyListing', [B2CPoilicyListingController::class, 'b2cPoilicyListing']);

    Route::post('channelMasterList', [CityMasterController::class, 'channelMasterList']);
    Route::post('branchMasterList', [CityMasterController::class, 'branchMasterList']);

    //corporate_email_whitelisting
    Route::post("corporate_email_whitelisting", [CorporatesController::class, 'corporateEmailWhitelisting']);

    Route::put('updateusertype', [UserTypeController::class, 'update_usertype']);
    //lob
    Route::group(['prefix' => 'lob'], function () {
        Route::get('/list', [LobMasterController::class, 'show']);
    });
    Route::post('/logoutAll', [LoginController::class, 'logoutAll']);


    Route::post('generate_login_token', [SSOController::class, 'create']);
    
    // Route::post('login_token_validate', [SSOController::class, 'TokenValidate']);
    Route::post('generate_login_token_hero_sso', [SSOController::class, 'generate']);
    Route::post('login_token_validate', [SSOController::class, 'loginTokenValidate']);

    
    Route::post('generate_landingPage_token', [TokenController::class, 'generateLandingPageToken']);

    Route::post('/api-generate-token', [TokenController::class, 'generateTokenApi']);

    // Protected API (requires valid token)
    Route::middleware('validate.token')->group(function () {
        Route::post('/create-users', [UserCreationController::class, 'store']);

    });

    // IPPB Back to Home redirect URL
    Route::get('redirectToIPPB', [IPPBSsoController::class, 'redirectToIPPB']);

    // Route::post('users/get_users_data', [UserController::class, 'getUsersData']);
    
    Route::post('/onboarding/generate_login_token', [PosOnboardingRedirectionController::class, 'generateLoginToken']);
    Route::get('/redirect_login_employee', [PosOnboardingRedirectionController::class, 'redirectLoginEmployee']);


    Route::post('getdata', [PullApiRapperController::class, 'getdata']);


    //-------------middleware auth with sanctum

    Route::middleware(['auth:sanctum', UpdateUserType::class])->group(function () {

        //Broker Details Api
        Route::get('/getBrokerDetails', [BrokerController::class, 'getBrokerDetails']);


        //POSP IC Mapping
        Route::post('generateToken', [PospIcMappingController::class, 'createToken']);
        Route::get('getPospData', [PospIcMappingController::class, 'getDetailpospData']);
        Route::get('get_pos_data', [PospIcMappingController::class, 'getDetailpospData']);


        // Route::post('/user_type', [UserTypeController::class, 'show_user_type']);
        // Route::post('/user_details', [LoginController::class, 'ListallUserDetails']);

        Route::group(['prefix' => 'template_master'], function () {
            Route::post('/store', [TemplateMasterController::class, 'store']);
            Route::get('/list', [TemplateMasterController::class, 'index']);
            Route::post('/deleteTemplate', [TemplateMasterController::class, 'destroy']);
            Route::put('/updateTemplate', [TemplateMasterController::class, 'update']);
        });
        Route::group(['prefix' => 'master_company'], function () {
            Route::post('/store', [MasterCompanyController::class, 'store']);
            Route::get('/list', [MasterCompanyController::class, 'show']);
            Route::post('/deleteCompany', [MasterCompanyController::class, 'destroy']);
            Route::post('/updateCompany', [MasterCompanyController::class, 'update']);
            Route::get('/master-companiesList', [MasterCompanyController::class, 'masterCompanies']);

        });
        //report configurator
        Route::post('/grouping-key-utility', [GroupingReportKeyUtilityController::class, 'store']);
        Route::post('/delete-grouping-key-utility', [GroupingReportKeyUtilityController::class, 'delete']);
        Route::post('/delete-Single-key', [GroupingReportKeyUtilityController::class, 'deleteSinglekey']);
        Route::post('/mis-report-configurator-getdata', [GroupingReportKeyUtilityController::class, 'misReportGroupGetData']);
        Route::post('/listReportData', [GroupingReportKeyUtilityController::class, 'listReportData']);


        Route::post('/getSellerData', [UserCreationController::class, 'getSellerData']);

        Route::post('/generatepostoken', [PosOnboardingRedirectionController::class, 'generatePosToken']);

        Route::post('/userMigrationApi', [DashboardUserMigrationController::class, 'migrate']);
        Route::post('/customerMigrationApi', [DashboardUserMigrationController::class, 'migrateCustomers']);
        Route::post('/migrateEmployee', [DashboardUserMigrationController::class, 'migrateEmployee']);

        //corporate_email_whitelisting
        Route::post("corporate_email_whitelisting", [CorporatesController::class, 'corporateEmailWhitelisting']);

        Route::put('updateusertype', [UserTypeController::class, 'update_usertype']);
        //lob
        Route::group(['prefix' => 'lob'], function () {
            Route::get('/list', [LobMasterController::class, 'show']);
        });
        Route::post('/updateLobData', [lobDataController::class, 'updateLobData']);
        Route::post('/lob-club', [LobMasterController::class, 'lobClub']);

        //mask configurator
        Route::group(['prefix' => 'excel-upload'], function () {
            Route::post('AddColumnToExcel', [ExcelKeyMasterController::class, 'AddColumnToExcel']);
            Route::post('excel_column_master', [ExcelKeyMasterController::class, 'excel_column_master']);
        });

        Route::group(['prefix' => 'maskconfiguration'], function () {
            Route::post('/add', [MaskConfiguratorController::class, 'maskConfiguratoradd']);
            Route::post('/delete', [MaskConfiguratorController::class, 'destroy']);
        });

        Route::post('/policy-expire/store', [PolicyExpireController::class, 'store']);
        Route::get('role-code-mapping/get-data-by-role', [RoleCodeMappingController::class, 'getDatabyRoleId']);
        Route::post('role-code-mapping/delete', [RoleCodeMappingController::class, 'delete']);

        Route::apiResource('role-code-mapping', RoleCodeMappingController::class);


        //status master
        Route::post('/create', [StatusMasterController::class, 'store']);
        Route::post('/createSst', [StatusMasterController::class, 'storeSst']);
        Route::post('/createSection', [StatusMasterController::class, 'storeSection']);
        Route::post('/createField', [StatusMasterController::class, 'storeField']);

        Route::put('/update', [StatusMasterController::class, 'update']);
        Route::put('/updateSst', [StatusMasterController::class, 'updateSst']);
        Route::put('/updateSection', [StatusMasterController::class, 'updateSection']);
        Route::put('/updateField', [StatusMasterController::class, 'updateField']);

        Route::post('/delete', [StatusMasterController::class, 'destroy']);
        Route::post('/deleteSst', [StatusMasterController::class, 'destroySst']);
        Route::post('/deleteSection', [StatusMasterController::class, 'destroySection']);
        Route::post('/deleteField', [StatusMasterController::class, 'destroyField']);

        Route::post("get_company_domain", [CorporatesController::class, 'getCompanyDomain']);
        Route::post("coporates_onbording", [CorporatesController::class, 'updateCorporatesData']);
        Route::post("addWhitelistEmail", [CorporatesController::class, 'addWhitelistEmail']);
        Route::post("addWhitelistDomain", [CorporatesController::class, 'addWhitelistDomain']);
        Route::post("get_domain", [CorporatesController::class, 'getDomain']);

        Route::post('policyDetails', [PolicyStatusController::class, 'policyDetails']);
        Route::post('/premiumFilter', [PolicyStatusController::class, 'premiumFilter']);

        // Reference Customer Lead
        Route::post('referenceCustomerLead', [CustomerDashboardController::class, 'referenceCustomerLead']);

        //Activity Report
        Route::post('/getActivityLogData', [ActivityLogController::class, 'getActivityLogData']);


        //MasterSchedulerConfig
        Route::post('/getSchedular', [MasterSchedulerConfigController::class, 'getSchedularData']);
        Route::post('/createSchedular', [MasterSchedulerConfigController::class, 'create']);
        Route::post('/editSchedular', [MasterSchedulerConfigController::class, 'edit']);
        Route::post('/updateSchedular', [MasterSchedulerConfigController::class, 'update']);
        Route::post('/deleteSchedular', [MasterSchedulerConfigController::class, 'delete']);
        //cron scheduler
        Route::post('/cronScheduler', [CronSchedulerController::class, 'index']);
 

        //Analytics controller
        Route::post('/analyticsDashboard', [AnalyticsController::class, 'analysis']);

        Route::get('filter', [CredentialController::class, 'filter']);

        Route::get('commissionRedirection ', [SSOController::class, 'ssoGenerateToken']);

        ////////// thirdpartygenerate middleware ////////
        //Posp utility
        // Route::middleware(['thirdpartygenerate.token'])->group(function (){
        Route::post('/posp-utility/fetch-master', [PospUtilityController::class, 'fetchData']);
        Route::post('/posp-utility/get-segments', [PospUtilityController::class, 'fetchSegement']);
        Route::post('/posp-utility/get-ic-by-segment', [PospUtilityController::class, 'fetchIcBySegement']);
        Route::post('/posp-utility/get-imd-mapping', [PospUtilityController::class, 'getImdMapping']);
        Route::post('/posp-utility/get-manf-id', [PospUtilityController::class, 'getManfId']);
        Route::post('/posp-utility/get-model-id', [PospUtilityController::class, 'getModelId']);
        Route::post('/posp-utility/get-fueltype', [PospUtilityController::class, 'getFueltype']);
        Route::post('/posp-utility/get-Variant', [PospUtilityController::class, 'getVariant']);
        Route::post('/posp-utility/get-mmv-mapping', [PospUtilityController::class, 'getMmvMapping']);
        Route::post('/posp-utility/add-mmv-utility', [PospUtilityController::class, 'addMmvUtility']);
        Route::post('/posp-utility/add-rto-utility', [PospUtilityController::class, 'addRtoUtility']);
        Route::post('/posp-utility/get-rto-mapping', [PospUtilityController::class, 'getRtoMapping']);
        Route::get('/posp-utility/get-rto-states', [PospUtilityController::class, 'getRtoStates']);
        Route::get('/posp-utility/get-statewise-rto', [PospUtilityController::class, 'statewiseRto']);
        Route::post('/posp-utility/add-ic-parameter', [PospUtilityController::class, 'addIcParameter']);
        Route::post('/posp-utility/update-record', [PospUtilityController::class, 'updateRecord']);
        Route::post('/posp-utility/add-imd-code', [PospUtilityController::class, 'addImdCode']);
        Route::post('/posp-utility/list-imd-code', [PospUtilityController::class, 'listImdCode']);
        Route::get('/posp-utility/excel-download-mmv', [PospUtilityController::class, 'excelDownloadMmv']);
        Route::post('/posp-utility/import-excel', [PospUtilityController::class, 'pospUtilityImportExcel']);
        Route::get('/posp-utility/get-users-by-usertype', [PospUtilityController::class, 'getUsersByUserType']);


        //Visibility Report Data
        Route::post('/visibilityReportData', [VisibilityReportDataController::class, 'visibilityReportData']);

        //visibility report details
        Route::post('/visibilityReportDetails', [VisibilityReportDataController::class, 'visibilityReportDetails']);
        //ReHitPdfController
        Route::post('/generate_rehit_pdf', [ReHitPdfController::class, 'generateRehitPdf']);

        Route::group(['prefix' => 'issuedPolicyDetails'], function () {
            Route::post('/issuedPolicesList', [IssuedPolicyController::class, 'issuedPolicesList']);
            Route::post('/editPolicy', [IssuedPolicyController::class, 'editPolicy']);
            Route::post('/updateIssuedPolices', [IssuedPolicyController::class, 'updateIssuedPolices']);
            Route::post('/cancelIssuedPolicy', [IssuedPolicyController::class, 'cancelIssuedPolicy']);
            Route::post('/policyDetailsUpdateLogs', [IssuedPolicyController::class, 'policyDetailsUpdateLogs']);
            Route::post('/policyDetailsCancelLogs', [IssuedPolicyController::class, 'policyDetailsCancelLogs']);
            Route::post('/getIcName', [IssuedPolicyController::class, 'getIcName']);
            Route::post('/getPolicyType', [IssuedPolicyController::class, 'getPolicyType']);
            Route::post('/getPolicyCategory', [IssuedPolicyController::class, 'getPolicyCategory']);
            Route::post('/getSellerUsername', [IssuedPolicyController::class, 'getSellerUsername']);
            Route::post('/getSellerDetails', [IssuedPolicyController::class, 'getSellerDetails']);


        });

        Route::post('/aadhaarSeedingCheck', [AdharPanLinkController::class, 'aadhaarSeedingCheck']);

        // });
        Route::get('/expired-token', [LoginController::class, 'expiredToken']);
        Route::get('/get-user', [LoginController::class, 'getUser']);
        Route::post('/login-counts', [LoginController::class, 'getLoginCounts']);
        Route::post('/login-user-counts', [LoginController::class, 'userLoginCounts']);
        Route::post('/getLoginCountForMappedUsers', [LoginController::class, 'getLoginCountForMappedUsers']);
        Route::post('/fetchMappedUserDetails', [LoginController::class, 'fetchMappedUserDetails']);
        Route::post('/loginTimeLogs', [LoginController::class, 'loginTimeLogs']);



        Route::group(['prefix' => 'customer_vehicle'], function () {
            Route::post('/store', [CustomerDashboardController::class, 'store']);
            Route::put('/update', [CustomerDashboardController::class, 'update']);
            Route::post('/delete', [CustomerDashboardController::class, 'destroy']);
            Route::get('/customVehicleList', [CustomerDashboardController::class, 'customVehicleList']);
            Route::post('/viewQuotesUrl', [CustomerDashboardController::class, 'viewQuotesUrl']);
        });
        Route::group(['prefix' => 'excel-upload'], function () {
            Route::get('/get-lob-wise-column', [ExcelKeyMasterController::class, 'get_column_lob_wise']);
            Route::post('AddColumnToExcel', [ExcelKeyMasterController::class, 'AddColumnToExcel']);
            Route::get('/download-excel', [ExcelKeyMasterController::class, 'DownloadExcel']);
            Route::post('/upload-excel', [ExcelKeyMasterController::class, 'UploadExcel']);
            Route::get('/list-excel-file', [ExcelKeyMasterController::class, 'listExcelFile']);
            Route::post('/mongoExcelUpload', [ExcelKeyMasterController::class, 'mongoExcelUpload']);
            Route::post('UpdateColumnNameToExcel', [ExcelKeyMasterController::class, 'UpdateColumnNameToExcel']);
            Route::post('excelColumnAdd', [ExcelKeyMasterController::class, 'excelColumnAdd']);
        });

        Route::group(['prefix' => 'lob'], function () {
            Route::post('/store', [lobDataController::class, 'store']);
        });

        Route::group(['prefix' => 'faq'], function () {
            Route::post('store', [FaqController::class, 'store']);
            Route::post('deleteFaq', [FaqController::class, 'destroy']);
            Route::put('updateFaq', [FaqController::class, 'update']);
            Route::post('listTag', [FaqController::class, 'listTag']);
        });
        Route::group(['prefix' => 'tags'], function () {
            Route::post('store', [TagNameController::class, 'store']);
            Route::post('deleteTag', [TagNameController::class, 'destroy']);
            Route::put('updateTag', [TagNameController::class, 'update']);
            Route::get('show', [TagNameController::class, 'show']);
        });
        Route::group(['prefix' => 'user-access-management'], function () {
            Route::post('store', [UserAccessManagementController::class, 'store']);
            Route::post('delete', [UserAccessManagementController::class, 'destroy']);
            Route::put('update', [UserAccessManagementController::class, 'update']);
            Route::get('list', [UserAccessManagementController::class, 'list']);
        });

        Route::post('/logout', [LoginController::class, 'customerLogout']);
        Route::post('/generate-token', [TokenController::class, 'generateToken']);
        Route::get('/generate-url', [TokenController::class, 'generateUrl']);
        Route::group(['prefix' => 'vehicle'], function () {
            Route::get('/list', [VehicleController::class, 'VehicleList']);
            Route::post('create', [VehicleController::class, 'create']);
            Route::put('update', [VehicleController::class, 'Update']);
        });
        Route::group(['prefix' => 'fuel'], function () {
            Route::get('/list', [FuelTypeController::class, 'VehicleList']);
            Route::post('create', [FuelTypeController::class, 'create']);
            Route::put('update', [FuelTypeController::class, 'Update']);
        });
        Route::group(['prefix' => 'users'], function () {
            Route::get('/list', [LoginController::class, 'ListallUser']);
            Route::get('/getUserList', [LoginController::class, 'getUserList']);
            Route::get('/getAllUserList', [LoginController::class, 'getAllUserList']);
            Route::post('create', [UserController::class, 'store']);
            Route::post('getBankDetails', [UserController::class, 'BankDetails']);
            Route::post('update', [UserController::class, 'update']);
            Route::post('delete', [UserController::class, 'destroy']);
            Route::post('/fetchUserDetails', [UserController::class, 'fetchUserDetails']);
            Route::post('/updateProfile', [UserController::class, 'updateProfile']);
            Route::post('/getReportingUsers', [UserController::class, 'getReportingUsers']);
            Route::post('/editUsers', [UserController::class, 'editUsers']);
            Route::post("UserExportData", [UserController::class, 'UserDataExport']);
            Route::post("updateUserMaping", [UserController::class, 'updateUserMaping']);
        });

        Route::group(['prefix' => 'newUsers'], function () {
            Route::post('create', [UserControllerNew::class, 'store']);
            Route::post('update', [UserControllerNew::class, 'update']);
            Route::get('userListing', [UserControllerNew::class, 'userListing']);
            Route::get('userListingNew', [UserControllerNew::class, 'userListingNew']);
            Route::post('/getReportingUsersNew', [UserController::class, 'getReportingUsersNew']);
            Route::post('/getDirectUserMapping', [UserControllerNew::class, 'getDirectUserMapping']);
            Route::post('/getDirectUserMappingTable', [UserControllerNew::class, 'getDirectUserMappingTable']);
            Route::post('/makeSupervisor', [UserControllerNew::class, 'makeSupervisor']);
            Route::post('/passwordUpdate', [UserControllerNew::class, 'passwordUpdate']);
            Route::post('/checkMobile', [UserControllerNew::class, 'checkMobile']);
            Route::post('/checkEmail',[UserControllerNew::class,'checkEmail']);
            Route::post('/searchUsers', [UserControllerNew::class, 'searchEmployee']);
            Route::post('/searchUsers-ByBranchCode', [UserControllerNew::class, 'searchEmployeeByBranchCode']);
            Route::get('/businessType', [UserControllerNew::class, 'businessType']);
            Route::get('/userListingData', [UserControllerNew::class, 'userListingData']);

        }); 

        Route::group(['prefix' => 'AUUsers'], function () {
            Route::get('userListing', [UserControllerAU::class, 'userListing']);
            Route::post('/passwordUpdate', [UserControllerAU::class, 'passwordUpdate']);
            Route::post('/checkMobile', [UserControllerAU::class, 'checkMobile']);
            Route::post('listDocuments',[UserControllerAU::class, 'listDocuments']);
            Route::post('updateDocuments',[UserControllerAU::class, 'UpdateDocuments']);
            Route::post('activate-user', [UserControllerAU::class, 'activateUser']);
        });

        Route::group(['prefix' => 'roles'], function () {
            Route::post('/create', [RolesController::class, 'store']);
            Route::get('/list', [RolesController::class, 'show']);
            Route::post('/delete', [RolesController::class, 'destroy']);
            Route::post('/assign', [RolesController::class, 'UserRoleMapping']);
            Route::post('/Clone', [RolesController::class, 'CreateClone']);
            Route::put('/edit', [RolesController::class, 'edit']);
            Route::post('/getReportingRoleData', [RolesController::class, 'getReportingRoleData']);
            Route::get('/roleList', [RolesController::class, 'roleList']);
            Route::get('/roleLowerHierarchyList', [RolesController::class, 'roleLowerHierarchyList']);
            Route::post('/rolesForReportConfigurator', [RolesController::class, 'rolesForReportConfigurator']);
            Route::get("/reportingUserReportsTo", [RolesController::class, 'reportingUserReportsTo']);
            Route::post('/reportingRoleNew', [RolesController::class, 'reportingRoleNew']);
            Route::get("/reportingEmployeeForPosAndPartner", [RolesController::class, 'reportingEmployeeForPosAndPartner']);

        });
        Route::group(['prefix' => 'UserType'], function () {
            Route::post('/create', [UserTypeController::class, 'store']);
            Route::get('/list', [UserTypeController::class, 'show']);
            Route::get('/filterUserTypeList', [UserTypeController::class, 'filterUserTypeList']);
            Route::put('/update', [UserTypeController::class, 'update']);
            Route::post('/delete', [UserTypeController::class, 'destroy']);
        });

        Route::post('/check-captcha', [CaptchaController::class, 'checkCaptcha'])->name('check.captcha');

        Route::group(['prefix' => 'MenuMaster'], function () {
            Route::post('/createMenu', [MenuMasterController::class, 'createMenu']);
            Route::post('/createSubMenu', [MenuMasterController::class, 'createSubMenu']);
            Route::post('/createSubChildMenu', [MenuMasterController::class, 'CreateSubChildMenu']);
            Route::get('/getMenu', [MenuMasterController::class, 'getMenu']);
            Route::get('/getSubMenu', [MenuMasterController::class, 'getSubMenu']);
            Route::post('/deleteMenu', [MenuMasterController::class, 'deleteMenu']);
            Route::delete('/deleteSubMenu', [MenuMasterController::class, 'deleteSubMenu']);
            Route::post('/updateSubMenu', [MenuMasterController::class, 'updateSubMenu']);
            Route::post('/updatMenuSequence', [MenuMasterController::class, 'updateMenuSequence']);
            Route::get('/download-document/{id?}', [DocumentConfigController::class, 'downloadDocument'])->name('downloadDocument');

        });

        Route::Group(['prefix' => 'AccessControl'], function () {
            Route::post('giveAccess', [AccessControllPermissionController::class, 'giveAccess']);
            Route::post('/delete', [AccessControllPermissionController::class, 'destroy']);
            Route::post('revokePermission', [AccessControllPermissionController::class, 'revokePermission']);
            Route::get('UserPermissions', [AccessControllPermissionController::class, 'UserPermissions']);
            Route::get('UserMenus', [AccessControllPermissionController::class, 'userMenus']);
            Route::post('getDataByFilter', [AccessControllPermissionController::class, 'getDataByFilter']);
            Route::post('deleteData', [AccessControllPermissionController::class, 'deleteData']);

        });

        Route::Group(['prefix' => 'PermissionAccess'], function () {
            Route::post('Create', [PermissionAccessController::class, 'store']);
            Route::get('GetAll', [PermissionAccessController::class, 'show']);
            Route::post('MapPermission', [PermissionAccessController::class, 'MapPermission']);
            Route::get('ListMapPermission', [PermissionAccessController::class, 'ListMapPermission']);
        });
        Route::Group(['prefix' => 'qualification'], function () {
            Route::post('store', [QualificationMasterController::class, 'store']);
            Route::get('list', [QualificationMasterController::class, 'QualificationList']);
            Route::put('update', [QualificationMasterController::class, 'update']);
            Route::post('delete', [QualificationMasterController::class, 'destroy']);
        });
        Route::group(['prefix' => 'Delegate'], function () {
            Route::post('Create', [DelegateMasterController::class, 'AllowUsers']);
            Route::post('map', [DelegateMasterController::class, 'MapUsers']);
            Route::post('SwitchDelegate', [DelegateMasterController::class, 'SwitchDelegate']);
            Route::post('GetUsers', [DelegateMasterController::class, 'getDelegateUsers']);
            Route::post('List', [DelegateMasterController::class, 'DelegateDetails']);
            Route::post('update', [DelegateMasterController::class, 'updateDelegateDetails']);
            Route::post('getDelegateLogs', [DelegateMasterController::class, 'getDelegateLogs']);
            Route::post('delete', [DelegateMasterController::class, 'delete']);
            Route::post('RevertToPreviousLogin', [DelegateMasterController::class, 'RevertToPreviousLogin']);

        });
        Route::get("ConfigSettingsList", [CredentialController::class, 'show']);
        Route::group(['prefix' => 'Permissions'], function () {
            Route::get('/get', [AccessControllPermissionController::class, 'getPermissions']);
        });

        Route::post('/create-template', [GroupingReportKeyUtilityController::class, 'createTemplate']);
        Route::post('/list-template', [GroupingReportKeyUtilityController::class, 'listTemplate']);
        Route::post('/edit-template', [GroupingReportKeyUtilityController::class, 'editTemplate']);
        Route::get('/get-template', [GroupingReportKeyUtilityController::class, 'getTemplate']);
        Route::get('/delete-template', [GroupingReportKeyUtilityController::class, 'DeleteTemplate']);
        Route::post('/save-reset-password', [LoginController::class, 'CustomerSaveResetPassword']);

        Route::group(['prefix' => 'sellNow'], function () {
            Route::post('sellNowUserType', [SellNowController::class, 'sellNowUserType']);
            Route::get('/lob-list-user-login', [SellNowController::class, 'LoginUserLobList']);
            Route::get('/pos-list', [SellNowController::class, 'posList']);
        });
        Route::get('/lob-club-list', [LobClubListController::class, 'LoginUserUniqueLobList']);

        Route::group(['prefix' => 'policystatus'], function () {
            Route::post('/policystatus', [PolicyStatusController::class, 'stages']);
            Route::post('/employeeList', [PolicyStatusController::class, 'employeeList']);
            Route::post('/filterData', [PolicyStatusController::class, 'filterData']);
            Route::post('/detailData', [PolicyStatusController::class, 'stages']);
            Route::post('/columnData', [PolicyStatusController::class, 'columnData']);
            Route::post('/columnDataUpdate', [PolicyStatusController::class, 'columnDataUpdate']);
            Route::post('/get_data', [PolicyStatusController::class, 'index']);
            Route::post('/uploadPolicyData', [PolicyUploadController::class, 'uploadPolicyData']);
            Route::post('/raise-query', [PolicyUploadController::class, 'raiseQuery']);
            Route::post('/shared_pdf',[PolicyUploadController::class, 'sharePdf']);
            Route::get('/getInspectionStatus',[PolicyStatusController::class, 'getInspectionStatus']);
        });
        Route::post('/role-details-list', [RolesController::class, 'roleDetailsList']);

        route::group(['prefix' => 'zone_master'], function () {
            Route::post('store', [ZoneMasterController::class, 'store']);
            Route::get('get_data', [ZoneMasterController::class, 'getData']);
            Route::post('edit/{id}', [ZoneMasterController::class, 'edit']);
            Route::post('update', [ZoneMasterController::class, 'update']);
            Route::post('delete', [ZoneMasterController::class, 'delete']);
            Route::post('vertical', [ZoneMasterController::class, 'vertical']);
            Route::post('vertical_master/delete', [ZoneMasterController::class, 'vertical_delete']);
            Route::post('vertical_master/update', [ZoneMasterController::class, 'vertical_update']);
        });

        Route::post('get_pdf', [getPdfController::class, 'getPdf']);
        Route::post('get_posp_details', [PospIcMappingController::class, 'getPospData']);
        Route::post('get_posp_list', [PospIcMappingController::class, 'getPospList']);
        Route::post('/UpdateStagePriority', [StageMasterController::class, 'updatePriorityStage']);
        Route::get('/list-stage', [StageMasterController::class, 'listStage']);

        Route::post('mis_report_filter', [PolicyStatusController::class, 'MisReportFilter']);
        Route::post('mis_report_Data', [PolicyStatusController::class, 'MisReportData']);

        Route::get('get_customer_data', [CustomerDataController::class, 'getCustomerData']);
        Route::post('getPolicyDetails', [CustomerDataController::class, 'getPolicyDetails']);
        Route::post('upcomingRenewals', [CustomerDataController::class, 'upcomingRenewals']);
        Route::get('getCustomerList', [CustomerDataController::class, 'getCustomerList']);
        Route::post('get_customer_recent_data', [CustomerDataController::class, 'getCustomerRecentData']);
        Route::post("UserExcelUpload", [UserDataUploadTemplateController::class, 'ExcelUserUpload']);
        Route::get("UserDataTemplate", [UserDataUploadTemplateController::class, 'DownloadExcelTemplate']);
        Route::get("renew_policy", [UserDataUploadTemplateController::class, 'renewPolicy']);
        Route::post('/editCustomerProfile', [CustomerDataController::class, 'editCustomerProfile']);
        Route::post('/viewCustomerPolicy', [CustomerDataController::class, 'viewCustomerPolicy']);
        Route::get('/customerLobs', [CustomerDataController::class, 'customerLobs']);
        Route::post('/customerDashboardData', [CustomerDataController::class, 'customerDashboardData']);

        
        Route::get('DashboardData', [DashboardApis::class, 'DashboardData']);
        Route::get('DashboardLobs', [DashboardApis::class, 'LobWiseStagePoliciesCount']);
        Route::get('AllCompanies', [DashboardApis::class, 'AllCompanies']);
        Route::post('IcWisePremium', [DashboardApis::class, 'IcWisePremium']);
        Route::post('monthWisePremium', [DashboardApis::class, 'monthWisePremium']);
        Route::post('userWisePremium', [DashboardApis::class, 'userWisePremium']);
        Route::post('customerWisePremium', [DashboardApis::class, 'customerWisePremium']);
        Route::post('topEmployee',[DashboardApis::class,'topEmployee']);
        Route::post('allTopUsers',[DashboardApis::class,'allTopUsers']);
        Route::post('topRanking',[DashboardApis::class,'topRanking']);
        Route::post('topRankingDetails',[DashboardApis::class,'topRankingDetails']);
        Route::post('topRankingDetailsHierarchy',[DashboardApis::class,'topRankingDetails']);
        Route::post('marquee' ,[DashboardApis::class,'Marquee']);
        Route::post('upcomingAndExpiredRenewals', [DashboardApis::class, 'upcomingAndExpiredRenewals']);
        Route::post('renewalTrend', [DashboardApis::class, 'renewalTrend']);
        Route::post('retrieveTraceIdData', [DashboardApis::class, 'retrieveTraceIdData']);
        Route::post('lobWisePolicyData', [DashboardApis::class, 'lobWisePolicyData']);
        Route::post('conversionRate', [DashboardApis::class, 'conversionRate']);
        Route::post('crossSell', [DashboardApis::class, 'lobWiseUniqueMobile']);
        Route::post('topLeaderBoard', [DashboardApis::class, 'topLeaderBoard']);
        Route::post('topUsers', [DashboardApis::class, 'topUsers']);
        Route::post('lifetimePremiumDetails', [DashboardApis::class, 'lifetimePremiumDetails']);
        Route::post('overAllConversionRate', [DashboardApis::class, 'overAllConversionRate']);
        Route::post('lobWiseTraceidList', [DashboardApis::class, 'lobWiseTraceidList']);
        Route::post('crossSellList', [DashboardApis::class, 'crossSellList']);

        Route::post('businessMetrics', [DashboardApis::class, 'businessMetrics']);
        Route::post('businessMetricsDetails', [DashboardApiNew::class, 'businessMetricsDetails']);
        Route::post('businessOperationDetails', [DashboardApiNew::class, 'businessOperationDetails']);

        Route::post('AuBranch',[UserControllerAU::class,'AuBranch']);
        Route::post('Auhierarchy',[UserControllerAU::class,'Auhierarchy']);

        Route::post('getRenewalLink', [RenewalController::class, 'getRenewalLink']);

        Route::post('getRenewalLink', [RenewalController::class, 'getRenewalLink']);

        Route::get('renewalConversionCount', [DashboardApis::class, 'renewalConversionCount']);
        Route::post('renewalConversionLobswiseCount', [DashboardApis::class, 'renewalConversionLobswiseCount']);
        Route::match(['get', 'post'], '/renewal-conversion', [DashboardApis::class, 'renewalConversionData']);

        Route::post('customerDetails', [DashboardApis::class, 'customerDetails']);
        Route::post('upcomingAndExpiredRenewalsDetails', [DashboardApis::class, 'upcomingAndExpiredRenewalsDetails']);

        Route::get('faqs/export', [FaqController::class, 'exportFaqs']);

        Route::post('upload-faqs', [FaqController::class, 'uploadFaqs']);
        Route::get('MispDownloadReport', [mispReportDownloadController::class, 'index']);

        //corporates on bording
        Route::group(['prefix' => 'coporates_on_bording'], function () {
            Route::post("newGetData", [CorporatesController::class, 'newGetData']);

            Route::post("getdata", [CorporatesController::class, 'getData']);
            Route::post("updateData", [CorporatesController::class, 'updateCorporatesData']);
            Route::post("whitelistingData", [CorporatesController::class, 'whiteListingCorporatesData']);
            Route::post("whitelistingDataView", [CorporatesController::class, 'whiteListingCorporatesDataView']);
            Route::post("deleteWhiteListingData", [CorporatesController::class, 'deleteWhiteListingCorporatesData']);
            Route::get("whitelistingDataSampleExcel", [CorporatesController::class, 'whiteListingCorporatesSampleExcel']);
            Route::post("editData", [CorporatesController::class, 'editCorporatesData']);
            Route::post("domainValidation", [CorporatesController::class, 'domainValidation']);
            Route::post("deleteData", [CorporatesController::class, 'deleteCorporatesData']);
            Route::post("updateDataStatus", [CorporatesController::class, 'updateCorporatesDataStatus']);
            Route::post("getCorporatesDomainList", [CorporatesController::class, 'whiteListingCorporatesDomainList']);
            Route::post("updateDomainList", [CorporatesController::class, 'updateCorporatesDataVerfication']);
            Route::post("updateWhiteListingUserStatus", [CorporatesController::class, 'updateWhiteListingUserStatus']);

        });

        Route::group(['prefix' => 'profile'], function () {
            Route::get("getData", [ProfileController::class, 'getData']);
            Route::post("updateProfile", [ProfileController::class, 'updateProfile']);
        });

        Route::group(['prefix' => 'cta_master'], function () {
            Route::get('createCta', [CtaMasterController::class, 'createCta']);
            Route::post('storeCta', [CtaMasterController::class, 'store']);
            Route::post('delete', [CtaMasterController::class, 'destroy']);
            Route::put('update', [CtaMasterController::class, 'update']);
            Route::get('filter', [CtaMasterController::class, 'show']);
            Route::get('getdata', [CtaMasterController::class, 'getData']);

        });

        Route::post('store', [OemMasterController::class, 'store']);
        Route::post('storeMisp', [OemMasterController::class, 'storeMisp']);
        Route::post('storeBranch', [OemMasterController::class, 'storeBranch']);
        Route::post('delete', [OemMasterController::class, 'destroy']);
        Route::put('update', [OemMasterController::class, 'updateMisp']);
        Route::get('showMisp', [OemMasterController::class, 'show']);
        Route::get('getOemList', [OemMasterController::class, 'getOemData']);
        Route::get('getMispList', [OemMasterController::class, 'getMispData']);
        Route::post('getHoData', [OemMasterController::class, 'getHoData']);

        Route::post('createOem', [OemMasterController::class, 'storeOem']);
        Route::post('getOem', [OemMasterController::class, 'indexOem']);
        Route::get('getOemListData', [OemMasterController::class, 'getOemList']);
        Route::post('deleteOem', [OemMasterController::class, 'destroyOem']);
        Route::put('updateOem', [OemMasterController::class, 'updateOem']);

        Route::post('storeMispData', [OemMasterController::class, 'storeMispData']);
        Route::post('ListMisp', [OemMasterController::class, 'ListMisp']);
        Route::get('getMispListData', [OemMasterController::class, 'getMispListData']);
        Route::post('deleteMisp', [OemMasterController::class, 'destroyMisp']);
        Route::put('updateMispData', [OemMasterController::class, 'updateMispData']);

        Route::post('storeMispBranch', [OemMasterController::class, 'storeMispBranch']);
        Route::post('mispBranchList', [OemMasterController::class, 'mispBranchList']);
        Route::post('deleteMispBranch', [OemMasterController::class, 'destroyMispBranch']);
        Route::put('updateMispBranch', [OemMasterController::class, 'updateMispBranch']);

        Route::post('storeState', [StateMasterController::class, 'storeState']);
        Route::post('stateList', [StateMasterController::class, 'stateList']);
        Route::post('deleteState', [StateMasterController::class, 'destroyState']);
        Route::put('updateState', [StateMasterController::class, 'updateState']);

        Route::post('storeCity', [StateMasterController::class, 'storeCity']);
        Route::post('cityList', [StateMasterController::class, 'cityList']);
        Route::post('deleteCity', [StateMasterController::class, 'destroyCity']);
        Route::put('updateCity', [StateMasterController::class, 'updateCity']);

        Route::post('storePinCode', [StateMasterController::class, 'storePinCode']);
        Route::post('pincodeList', [StateMasterController::class, 'pincodeList']);
        Route::post('deletePincode', [StateMasterController::class, 'destroyPincode']);
        Route::put('updatePincode', [StateMasterController::class, 'updatePincode']);
        Route::post('getPincodeDetails', [PincodeMasterController::class, 'getPincodeDetails']);

        Route::post('fetchCity', [StateMasterController::class, 'fetchCity']);

        //Broker Details Api
        Route::post('createBroker', [BrokerController::class, 'createBroker']);
        Route::post('updateBrokerDetails/{id}', [BrokerController::class, 'updateBrokerDetails']);
        Route::post('deleteBrokerDetails/{id}', [BrokerController::class, 'deleteBrokerDetails']);

        Route::post('createPartner', [PartnerController::class, 'createPartner']);
        Route::post('getPartnerDetails', [PartnerController::class, 'getPartnerDetails']);


        Route::post('getdata', [PullApiRapperController::class, 'getdata']);
        Route::get('LogsApiList', [LogsApiController::class, 'LogsApiList']);

        // POSP IC Mapping
        Route::post('/icMappingSample', [PospIcMappingController::class, 'icMappingSample']);
        Route::post('/pospIcMappingUpload', [PospIcMappingController::class, 'pospIcMappingUpload']);
        Route::get('/pospIcMappings', [PospIcMappingController::class, 'getAllPospIcMappings']);

        Route::post('offlinePolicySampleExcel', [ExcelKeyMasterController::class, 'offlinePolicySampleExcel']);

        Route::get('/searchRoles', [RolesController::class, 'searchRoles']);

        //Claim Master:
        Route::get('getAccidentsData', [ClaimMasterController::class, 'index']);
        Route::get('accidentDropdown', [ClaimMasterController::class, 'dropdown']);
        Route::post('addAccidentsData', [ClaimMasterController::class, 'store']);
        Route::post('updateAccidents/{id}', [ClaimMasterController::class, 'update']);
        Route::post('deleteAccidents/{id}', [ClaimMasterController::class, 'destroy']);

        Route::get('getAllData', [ClaimMasterController::class, 'indexData']);
        Route::get('getVehiclePartsData', [ClaimMasterController::class, 'getVehiclePartsData']);
        Route::post('storeData', [ClaimMasterController::class, 'storeData']);
        Route::post('updateData/{id}', [ClaimMasterController::class, 'updateData']);
        Route::post('delete/{id}', [ClaimMasterController::class, 'delete']);

        Route::prefix('license_types')->group(function () {
            Route::get('/dropdown', [ClaimMasterController::class, 'getLicenseDropdown']);
            Route::get('/getLicenseTypeData', [ClaimMasterController::class, 'listLicenseTypes']);
            Route::post('/addLicenseType', [ClaimMasterController::class, 'addLicenseType']);
            Route::post('/editLicenseType/{id}', [ClaimMasterController::class, 'editLicenseType']);
            Route::post('/removeLicenseType/{id}', [ClaimMasterController::class, 'removeLicenseType']);
        });

        // Claim Management
        Route::post('claimDataSearch', [ClaimMasterController::class, 'claimDataSearch']);
        Route::post('createClaim', [ClaimMasterController::class, 'createClaim']);
        Route::post('claimList', [ClaimMasterController::class, 'claimList']);
        Route::post('getClaimPolicyDetails', [ClaimMasterController::class, 'getClaimPolicyDetails']);

        Route::post('createCatastrophy', [ClaimMasterController::class, 'createCatastrophy']);
        Route::post('deleteCatastrophy', [ClaimMasterController::class, 'deleteCatastrophy']);
        Route::post('getClaimId', [ClaimMasterController::class, 'getClaimId']);
        Route::post('createClaimManagement', [ClaimMasterController::class, 'createClaimManagement']);
        Route::post('stagesList', [ClaimMasterController::class, 'stagesList']);
        Route::post('listCatastrophy', [ClaimMasterController::class, 'listCatastrophy']);
        Route::post('getClaimManagement', [ClaimMasterController::class, 'getClaimManagement']);
        Route::post('getCatastrophy', [ClaimMasterController::class, 'getCatastrophy']);

        Route::post('CustomerList', [UserControllerNew::class, 'CustomerList']);

        Route::post('manageUserAccess', [UserControllerNew::class, 'manageUserAccess']);
        Route::post('prefillManageAccessData', [UserControllerNew::class, 'prefillManageAccessData']);

        // Reference Customer Lead
        Route::post('referenceCustomerLead', [CustomerDashboardController::class, 'referenceCustomerLead']);

        Route::post('getreferenceCustomerLead', [CustomerDashboardController::class, 'getreferenceCustomerLead']);
        Route::post('exportReferenceCustomer', [CustomerDashboardController::class, 'exportReferenceCustomer']);

        Route::resource('offlineUploadPolicy', OfflineUploadPolicyController::class);
        Route::post('offlinePolicyDoc', [OfflineUploadPolicyController::class, 'offlinePolicyDoc']);
        Route::post('offlinePolicyStatus/{id}', [OfflineUploadPolicyController::class, 'offlinePolicyStatus']);
        Route::get('showPolicyList', [OfflineUploadPolicyController::class, 'showPolicyList']);
        Route::get('motorLobMappinglist', [MotorLobMappingController::class, 'index']);
        Route::post('storeMapping', [MotorLobMappingController::class, 'store']);
        Route::post('updateMapping/{id}', [MotorLobMappingController::class, 'update']);
        Route::delete('deleteMapping/{id}', [MotorLobMappingController::class, 'destroy']);

        //Theme Configuration
        Route::post('/storeTheme', [ThemeMasterController::class, 'storeTheme']);
        Route::post('/updateTheme', [ThemeMasterController::class, 'updateTheme']);
        Route::post('/deleteTheme', [ThemeMasterController::class, 'deleteTheme']);
        Route::post('/getTheme', [ThemeMasterController::class, 'getTheme']);

        //Claim Master:
        Route::get('getAccidentsData', [ClaimMasterController::class, 'index']);
        Route::get('accidentDropdown', [ClaimMasterController::class, 'dropdown']);
        Route::post('addAccidentsData', [ClaimMasterController::class, 'store']);
        Route::post('updateAccidents/{id}', [ClaimMasterController::class, 'update']);
        Route::post('deleteAccidents/{id}', [ClaimMasterController::class, 'destroy']);

        Route::get('getAllData', [ClaimMasterController::class, 'indexData']);
        Route::get('getVehiclePartsData', [ClaimMasterController::class, 'getVehiclePartsData']);
        Route::post('storeData', [ClaimMasterController::class, 'storeData']);
        Route::post('updateData/{id}', [ClaimMasterController::class, 'updateData']);
        Route::post('delete/{id}', [ClaimMasterController::class, 'delete']);

        Route::prefix('license_types')->group(function () {
            Route::get('/dropdown', [ClaimMasterController::class, 'getLicenseDropdown']);
            Route::get('/getLicenseTypeData', [ClaimMasterController::class, 'listLicenseTypes']);
            Route::post('/addLicenseType', [ClaimMasterController::class, 'addLicenseType']);
            Route::post('/editLicenseType/{id}', [ClaimMasterController::class, 'editLicenseType']);
            Route::post('/removeLicenseType/{id}', [ClaimMasterController::class, 'removeLicenseType']);
        });

        // Claim Management
        Route::post('claimDataSearch', [ClaimMasterController::class, 'claimDataSearch']);
        Route::post('createClaim', [ClaimMasterController::class, 'createClaim']);
        Route::post('claimList', [ClaimMasterController::class, 'claimList']);
        Route::post('getClaimPolicyDetails', [ClaimMasterController::class, 'getClaimPolicyDetails']);

        Route::post('createCatastrophy', [ClaimMasterController::class, 'createCatastrophy']);
        Route::post('deleteCatastrophy', [ClaimMasterController::class, 'deleteCatastrophy']);
        Route::post('getClaimId', [ClaimMasterController::class, 'getClaimId']);
        Route::post('createClaimManagement', [ClaimMasterController::class, 'createClaimManagement']);
        Route::post('stagesList', [ClaimMasterController::class, 'stagesList']);
        Route::post('listCatastrophy', [ClaimMasterController::class, 'listCatastrophy']);
        Route::post('getClaimManagement', [ClaimMasterController::class, 'getClaimManagement']);
        Route::post('getCatastrophy', [ClaimMasterController::class, 'getCatastrophy']);

        //Video Blog Master
        Route::post('/createVideosBlogs', [VideoBlogsMasterController::class, 'storeVideoBlogData']);
        Route::post('/updateVideosBlogs', [VideoBlogsMasterController::class, 'updateVideoBlogData']);
        Route::post('/getVideosBlogs', [VideoBlogsMasterController::class, 'getVideoBlogData']);
        Route::post('/deleteVideoBlogData', [VideoBlogsMasterController::class, 'deleteVideoBlogData']);



        //BroadCast Module
        Route::post('/storeBroadcastData', [BroadcastMasterController::class, 'storeBroadcastData']);
        Route::post('/updateBroadcastData', [BroadcastMasterController::class, 'updateBroadcastData']);
        Route::post('/getBroadcastData', [BroadcastMasterController::class, 'getBroadcastData']);
        Route::post('/deleteBroadcastData', [BroadcastMasterController::class, 'deleteBroadcastData']);
        Route::post('/broadcastPopupList', [BroadcastMasterController::class, 'broadcastPopupList']);

        //Multi User Login
        Route::post('/newSwitchUser', [MultiUserLoginController::class, 'newSwitchUser']);
        Route::post('switchUser', [MultiUserLoginController::class, 'switchUser']);

        Route::post('ssoDashboardListing', [UserControllerNew::class, 'ssoDashboardListing']);
        Route::post('ssoMotorTokenListing', [UserControllerNew::class, 'ssoMotorTokenListing']);

        // Commision Model Masters APIs
        Route::post('vehicleType', [CommissionController::class, 'vehicleType']);
        Route::post('vehicleSubType', [CommissionController::class, 'vehicleSubType']);
        Route::post('rto', [CommissionController::class, 'rto']);
        Route::post('state', [CommissionController::class, 'state']);
        Route::post('city', [CommissionController::class, 'city']);
        Route::post('businessType', [CommissionController::class, 'businessType']);
        Route::post('policyType', [CommissionController::class, 'policyType']);
        Route::post('vehicleMake', [CommissionController::class, 'vehicleMake']);
        Route::post('vehicleModel', [CommissionController::class, 'vehicleModel']);
        Route::post('fuelType', [CommissionController::class, 'fuelType']);
        Route::post('insuranceCompanyMaster', [CommissionController::class, 'insuranceCompanyMaster']);
        Route::post('seatingCapacity', [CommissionController::class, 'seatingCapacity']);
        Route::post('noOfWheels', [CommissionController::class, 'noOfWheels']);
        Route::post('gvwRange', [CommissionController::class, 'gvwRange']);
        Route::post('brokerageCalculation', [CommissionController::class, 'brokerageCalculation']);
        Route::post('ImportAuHierarchyDump', [MasterCompanyController::class, 'ImportAuHierarchyDump']);

        
        //Masking
        Route::post('getPiFields', [MaskDataController::class, 'getPiFields']);


        Route::post('maskingTypeList', [MaskDataController::class, 'maskingTypeList']);
        Route::post('storeMaskingType', [MaskDataController::class, 'storeMaskingType']);
        Route::post('updateMaskingType', [MaskDataController::class, 'updateMaskingType']);
        Route::post('deleteMaskingType', [MaskDataController::class, 'deleteMaskingType']);

        Route::post('maskingConfigurator', [MaskDataController::class, 'maskingConfigurator']);     //Create
        Route::post('maskConfigurationMasterList', [MaskDataController::class, 'maskConfigurationMasterList']);   //List
        Route::post('editmaskingConfigurator', [MaskDataController::class, 'editmaskingConfigurator']);   //Edit


        Route::post('getVisibilityDownloadedReport', [VisibilityReportDataController::class, 'getVisibilityDownloadedReport']);   

    });

});

});




