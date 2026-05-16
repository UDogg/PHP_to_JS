<?php

use App\Http\Controllers\DecryptionModule\DecryptionController;
use App\Http\Controllers\SmsActivityLogControllerNew;
use Illuminate\Support\Facades\Route;
use App\Http\Controllers\RunMigration;
use App\Http\Controllers\FaqController;
use App\Http\Controllers\EventController;
use App\Http\Controllers\RolesController;
use App\Http\Controllers\TokenController;
use App\Http\Controllers\lobDataController;
use App\Http\Controllers\LogsApiController;
use App\Http\Controllers\TagNameController;
use App\Http\Controllers\SyncDataController;
use App\Http\Controllers\UserTypeController;
use App\Http\Controllers\CtaMasterController;
use App\Http\Controllers\LobMasterController;
use App\Http\Controllers\OemMasterController;
use App\Http\Controllers\User\UserController;
use App\Http\Controllers\FormMasterController;
use App\Http\Controllers\KeyUtilityController;
use App\Http\Controllers\MongoKeyUtilityController;
use App\Http\Controllers\MenuMasterController;
use App\Http\Controllers\SqlRunnnerController;
use App\Http\Controllers\User\LoginController;
use App\Http\Controllers\ZoneMasterController;
use App\Http\Controllers\FormBuilderController;
use App\Http\Controllers\Master\MenuController;
use App\Http\Controllers\SmsTemplateController;
use App\Http\Controllers\StageMasterController;
use App\Http\Controllers\StatusMasterController;
use App\Http\Controllers\User\CaptchaController;
use App\Http\Controllers\Master\BrokerController;
use App\Http\Controllers\MasterCompanyController;
use App\Http\Controllers\DocumentConfigController;
use App\Http\Controllers\SmsActivityLogController;
use App\Http\Controllers\TemplateMasterController;
use App\Http\Controllers\EmailActivityLogController;
use App\Http\Controllers\Master\OtpMasterController;
use App\Http\Controllers\PermissionAccessController;
use App\Http\Controllers\VisibilityReportController;
use App\Http\Controllers\Master\CredentialController;
use Rap2hpoutre\LaravelLogViewer\LogViewerController;

use App\Http\Controllers\Master\SessionTimeController;
// use App\Http\Controllers\SmsActivityLogController;
use App\Http\Controllers\QualificationMasterController;
use App\Http\Controllers\Master\UiCustomizationController;
use App\Http\Controllers\Master\MaskConfiguratorController;
use App\Http\Controllers\AccessControllPermissionController;
use App\Http\Controllers\PolicyStatusFilterMasterController;
use App\Http\Controllers\MasterPolicy\PolicyStatusController;
use App\Http\Controllers\OfflineExcelUpload\ExcelKeyMasterController;
use App\Http\Controllers\ReportConfigurator\GroupingReportKeyUtilityController;
use App\Http\Controllers\ExcelKeyColumnController;
use App\Http\Controllers\PincodeMasterController;
use App\Http\Controllers\CityMasterController;
use App\Http\Controllers\NewStateMasterController;
use App\Http\Controllers\MotorLobMappingController;
use App\Http\Controllers\EmailtemplateController;
use App\Http\Controllers\MarqueeController;
use App\Http\Controllers\MisColumnViewController;
use App\Http\Controllers\MaskDataController;
Route::get('/', function () {
    return response()->json([
        'status'  => false,
        'message' => 'You do not have permission to access to this resource.',
    ]);
});


Route::post('/cron/posupload', [UserController::class, 'PospUploadData']);
Route::post('/validate_token', [TokenController::class, 'validateToken']);
Route::get('lob_data', [lobDataController::class, 'index'])->name('lob_data');
Route::get('company_list', [MasterCompanyController::class, 'index'])->name('company_list');
Route::post('/check-captcha', [CaptchaController::class, 'checkCaptcha'])->name('check.captcha');
Route::get('/reload-captcha', [CaptchaController::class, 'reloadCaptcha']);
Route::get('/console', [LoginController::class, 'loginForm'])->name('login');
Route::post('console', [LoginController::class, 'login'])->name('auth.login');
Route::post('new-login', [LoginController::class, 'resetPassword'])->name('auth.resetPassword');
Route::post('/send-otp', [LoginController::class, 'sendOtp'])->name('auth.sendOtp');
Route::get('/verify_totp', [LoginController::class, 'showTOtpForm'])->name('totp');
Route::post('verify_totp', [LoginController::class, 'verifyTOtp']);
Route::get('request_email', [UserController::class, 'showEmailIdForm'])->name('admin.emailRequest');
Route::post('request_email', [UserController::class, 'resendQrCode']);
Route::get('/reset-password', [LoginController::class, 'forgetPassword']);
Route::get('/email-logs', [EmailActivityLogController::class, 'index'])->name('email.logs.index');
Route::get('/show-email-logs', [EmailActivityLogController::class, 'show'])->name('email_logs.show');
Route::get('/sms-logs', [SmsActivityLogController::class, 'index'])->name('sms.logs.index');
Route::get('/sms-logs', [SmsActivityLogController::class, 'index'])->name('smsLogs');
Route::get('/run_migration', [RunMigration::class, 'index']);
Route::get('/dbseed', [RunMigration::class, 'dbseed']);
Route::get('/optimizeclear', [RunMigration::class, 'optimizeclear']);
Route::get('/runJobs', [RunMigration::class, 'runJobs']);
Route::get('/mask-configuration', [MaskConfiguratorController::class, 'index']);

Route::middleware(['auth'])->group(function () {
    Route::Resource('excel_column', ExcelKeyColumnController::class);
    Route::post('add_column', [ExcelKeyColumnController::class, 'add_column'])->name('add_column');
    Route::Resource('pincode_master', PincodeMasterController::class);
    Route::Resource('city_master', CityMasterController::class);
    Route::Resource('state_master', NewStateMasterController::class);

    Route::get('/error-view', [LogViewerController::class, 'index']); // log viewer
    Route::get('/smsActivityLogList', [SmsActivityLogControllerNew::class, 'index'])->name('smsActivityLog.index');
    Route::get('/smsActivityLogCreate', [SmsActivityLogControllerNew::class, 'create'])->name('smsActivityLog.create');
    Route::post('/smsActivityLogStore', [SmsActivityLogControllerNew::class, 'store'])->name('smsActivityLog.store');
    Route::get('/smsActivityLogEdit/{id}', [SmsActivityLogControllerNew::class, 'smsEdit'])->name('smsActivityLog.edit');
    Route::put('/smsActivityLogUpdate/{id}', [SmsActivityLogControllerNew::class, 'smsUpdate'])->name('smsActivityLog.Update');
    Route::post('/smsActivityLogDelete/{id}', [SmsActivityLogControllerNew::class, 'delete'])->name('smsActivityLog.destroy');
    Route::get('/sms-activity-log-export', [SmsActivityLogControllerNew::class, 'export'])->name('smsActivityLog.export');




    Route::resource('user', UserController::class);

    Route::get('user/{id}/edit-doc', [UserController::class, 'editUserDoc'])->name('user.editUserDoc');

    Route::post('user/update-doc/{id}', [UserController::class, 'updateUserDoc'])->name('user.updateUserDoc');
    
    Route::post('/user/restore/{id}', [UserController::class, 'restore'])->name('user.restore');

    Route::get('logout', [LoginController::class, 'logout'])->name('logout');
    Route::view('/', 'dashboard')->name('dashboard');
    Route::view('/adminlte', 'adminlte')->name('adminlte');
    Route::resource('menu', MenuController::class);
    Route::resource('credential', CredentialController::class);
    Route::post('credential/AddConfig', [CredentialController::class, 'AddConfig']);
    Route::post('credential/filter', [CredentialController::class, 'filter']);
    Route::resource('broker', BrokerController::class);
    Route::resource('marquee',MarqueeController::class);
    Route::resource('template', TemplateMasterController::class);
    Route::resource('session', SessionTimeController::class);
    Route::resource('otp', OtpMasterController::class);
    Route::put('/otp/{id}', [OtpMasterController::class, 'update'])->name('otp.update');
    Route::resource('placeholder', UiCustomizationController::class);
    Route::resource('sms_template', SmsTemplateController::class);
    Route::resource('event', EventController::class);
    Route::get('template/{template}/logs', [TemplateMasterController::class, 'showLogs'])->name('template.logs');
    Route::resource('stagemaster', StageMasterController::class);
    Route::post('/UpdateStagePriority', [StageMasterController::class, 'updatepriority'])->name('UpdateStagePriority');
    Route::post('/sub_stage', [StageMasterController::class, 'create_subStage'])->name('sub_stage');
//    Route::post('edit_sub_stage', [StageMasterController::class, 'edit_subStage'])->name('edit_sub_stage');
    Route::post('del_sub_stage', [StageMasterController::class, 'delete_subStage'])->name('del_sub_stage');
    Route::post('StageRenewal', [StageMasterController::class, 'StageRenewal'])->name('StageRenewal');
    Route::get('policystatus', [PolicyStatusController::class, 'index'])->name('policystatus');
    Route::post('/policystatus', [PolicyStatusController::class, 'stages']);
    // Route::post('/download', [PolicyStatusController::class, 'stages']);
    Route::get('policystatus_renewal', [PolicyStatusController::class, 'index'])->name('policystatus_renewal');
    Route::post('policystatus_renewal', [PolicyStatusController::class, 'stages'])->name('policystatus_renewal');
    Route::get('document_upload_config', [DocumentConfigController::class, 'documentConfigIndex'])->name('documentConfigIndex');
    Route::post('uploadDocument', [DocumentConfigController::class, 'uploadDocument'])->name('uploadDocument');
    Route::get('documents/{id}/edit', [DocumentConfigController::class, 'edit'])->name('document.edit');
    Route::put('documents/{id}', [DocumentConfigController::class, 'update'])->name('document.update');
    Route::delete('documents/{id}', [DocumentConfigController::class, 'destroy'])->name('document.delete');
    Route::get('/download-document/{id?}', [DocumentConfigController::class, 'downloadDocument'])->name('downloadDocument');




    Route::get('zone_master', [ZoneMasterController::class, 'index'])->name('zone_master');
    Route::post('zone_master', [ZoneMasterController::class, 'store'])->name('zone_master');
    Route::get('zone_master/edit/{id}', [ZoneMasterController::class, 'edit'])->name('edit');
    Route::put('zone_master/update', [ZoneMasterController::class, 'update'])->name('update');
    Route::post('zone_master/delete', [ZoneMasterController::class, 'delete'])->name('delete');
    Route::post('zone_master/vertical', [ZoneMasterController::class, 'vertical'])->name('vertical');
    Route::post('zone_master/vertical_master/delete', [ZoneMasterController::class, 'vertical_delete'])->name('delete_vertical');
    Route::post('zone_master/vertical_master/update', [ZoneMasterController::class, 'vertical_update'])->name('update_vertical');

    route::get('visibility_report', [VisibilityReportController::class, 'index'])->name('visibility_report');
    route::post('visibility_report/getdata', [VisibilityReportController::class, 'getData'])->name('getdata');
    route::post('visibility_report/edit', [VisibilityReportController::class, 'motordataview'])->name('edit');
    route::post('visibility_report/download', [VisibilityReportController::class, 'download'])->name('download');

    Route::group(['prefix' => 'excel-upload'], function () {
        Route::get('column_master', [ExcelKeyMasterController::class, 'column_master'])->name('excel_column_master');
        Route::post('column_master', [ExcelKeyMasterController::class, 'column_master'])->name('excel_column_master');
        Route::get('excel_column_master', [ExcelKeyMasterController::class, 'excel_column_master'])->name('excel_column_master_show');
        Route::post('excel_column_master', [ExcelKeyMasterController::class, 'excel_column_master'])->name('excel_column_master_show');
        Route::post('AddColumnToExcel', [ExcelKeyMasterController::class, 'AddColumnToExcel']);
        Route::post('UpdateColumnNameToExcel', [ExcelKeyMasterController::class, 'UpdateColumnNameToExcel']);
    });
    Route::group(['prefix' => 'PolicyStatus'], function () {
        Route::get('column_master', [PolicyStatusController::class, 'column_master'])->name('policystatus_column_master');
        Route::post('column_master', [PolicyStatusController::class, 'column_master'])->name('lob_wise_filter_column_master');
        Route::post('update_column_master', [PolicyStatusController::class, 'update_column_master'])->name('update_column_master');
        Route::post('Enable_columns', [PolicyStatusController::class, 'Enable_columns'])->name('Enable_columns');
        Route::post('DefaultColumns', [PolicyStatusController::class, 'set_default']);
        Route::get('cta_master', [CtaMasterController::class, 'index'])->name('cta_master');
    });
    Route::resource('UserTypes', UserTypeController::class);
    Route::post('createUserType',[ UserTypeController::class,'createUserType'])->name('UserTypes.createUserType');
    Route::resource('roles', RolesController::class);
    Route::group(['prefix' => 'lob'], function () {
        Route::get('/', [LobMasterController::class, 'index'])->name('lob');
        Route::post('/enable', [LobMasterController::class, 'update'])->name('lob_enable');
    });
    Route::group(['prefix' => 'Permission'], function () {
        Route::get('/', [PermissionAccessController::class, 'index'])->name('PermissionView');
    });
    Route::group(['prefix' => 'AccessControl'], function () {
        Route::get('/', [AccessControllPermissionController::class, 'index'])->name('AccessControlView');
        Route::post('/store', [AccessControllPermissionController::class, 'store'])->name('createPermission');
        Route::post('/giveAccess', [AccessControllPermissionController::class, 'giveAccess'])->name('GiveAccess');
        Route::post('/delete', [AccessControllPermissionController::class, 'destroy'])->name('delete');
        Route::post('/revokePermission', [AccessControllPermissionController::class, 'destroy'])->name('delete');
    });
    Route::group(['prefix' => 'email-templates'],function(){
        Route::get('/',[EmailtemplateController::class,'show'])->name('Email-Template-Index');
        Route::get('/add',[EmailtemplateController::class,'add'])->name('Email-template-add');
        Route::post('/store',[EmailtemplateController::class,'store'])->name('Email-template-store');
        Route::delete('delete/{id}',[EmailtemplateController::class,'delete'])->name('email-templates.delete');
        Route::get('update/{id}',[EmailtemplateController::class,'updatepage'])->name('email-templates.update');
        Route::post('store/update/{id}',[EmailtemplateController::class,'storeUpdate'])->name('updated-Email-template');
        Route::post('/search',[EmailtemplateController::class,'search'])->name('email-template.search');
    });
    Route::group(['prefix' => 'MenuMaster'], function () {
        Route::get('/', [MenuMasterController::class, 'index'])->name('MenuMaster');
        Route::get('/SubMenu', [MenuMasterController::class, 'index']);
    });

    Route::resource('KeyUtility', KeyUtilityController::class);
    Route::resource('mongo-key-utility', MongoKeyUtilityController::class);
    Route::get('/miscolumnview', [MisColumnViewController::class, 'index'])->name('miscolumnview.index');
    Route::prefix('miscolumnview')->group(function () {
    Route::get('/mongo-keys', [MisColumnViewController::class, 'getMongoKeys']);
    Route::post('/store', [MisColumnViewController::class, 'store'])->name('miscolumnview.store');
    Route::post('/update/{id}', [MisColumnViewController::class, 'update']);
    Route::delete('/delete/{id}', [MisColumnViewController::class, 'delete']);
    });

    Route::resource('reportKeyUtility', GroupingReportKeyUtilityController::class);
    Route::post('/update-priority', [GroupingReportKeyUtilityController::class, 'updatePriority'])->name('update.priority');

    Route::put('/reportKeyUtility/{name}', [GroupingReportKeyUtilityController::class, 'update'])->name('reportKeyUtility.update');
    Route::get('SqlRunner', [SqlRunnnerController::class, 'index'])->name('SqlRunner');
    Route::post('SqlRunner', [SqlRunnnerController::class, 'ExecuteSql'])->name('RunSql');
    Route::resource('PolicyStatusFilterMaster', PolicyStatusFilterMasterController::class);
    Route::post('GetColumns', [PolicyStatusFilterMasterController::class, 'GetColumns'])->name('GetColumns');
    Route::post('/PolicyStatusFilterMaster/update', [PolicyStatusFilterMasterController::class, 'update']);
    Route::delete('/PolicyStatusFilterMaster_delete/{id}', [PolicyStatusFilterMasterController::class, 'delete'])->name('PolicyStatusFilterMaster.delete');

    Route::get('form_builder', [FormBuilderController::class, 'index'])->name('form_builder');
    Route::post('update_form', [FormBuilderController::class, 'update'])->name('update_form');

    Route::get('/decrypt-form', [DecryptionController::class, 'index'])->name('decrypt.form');
    Route::post('/decrypt-response', [DecryptionController::class, 'decrypt'])->name('decrypt.payload');
    Route::post('/encrypt-request', [DecryptionController::class, 'encrypt'])->name('encrypt.request');

    route::get('form_master', [FormMasterController::class, 'index'])->name('form_master');
    route::post('get_items', [FormMasterController::class, 'getItems'])->name('get_items');
    route::post('submit_form', [FormMasterController::class, 'submitForm'])->name('submit_form');

    Route::post('show_form', [FormMasterController::class, 'show'])->name('show_form');
    Route::get('edit/{id}', [FormMasterController::class, 'edit'])->name('edit_form');
    Route::post('update/{id}', [FormMasterController::class, 'update'])->name('update_form');
    Route::delete('delete/{id}', [FormMasterController::class, 'destroy'])->name('destroy_form');
    Route::get('PolicyReportDownload/{uid}', [App\Http\Controllers\DataExportController::class, 'validateFile'])->name('PolicyReportDownload');

    Route::resource('motorLobMapping', MotorLobMappingController::class);

});
Route::get('sync-data', SyncDataController::class);
Route::view('/login-with-otp', 'auth.loginwithotp')->name('login.with.otp');
Route::view('/login-with-password', 'auth.passwordForm')->name('login.with.password');
Route::view('/login-with-forget-password', 'auth.forgetpassword')->name('login.with.forget.password');

// Route::post('/login-with-otp-post', [LoginController::class, 'loginwithotppost'])->name('login.with.otp.post');
// Route::view('/confirm-login-with-otp', 'auth.confirmloginwithotp')->name('confirm.login.with.otp');
// Route::get('/communication', function () {
//     return view('communication');
// })->name('communication');
// Route::post('/template/store', [TemplateMasterController::class, 'sendEmail'])->name('template.store');
Route::post('/template/store', [TemplateMasterController::class, 'store'])->name('template.store');

Route::post('/login-with-otp-post', [LoginController::class, 'loginw
    ithotppost',])->name('login.with.otp.post');
Route::view('/confirm-login-with-otp', 'auth.confirmloginwithotp')->name('confirm.login.with.otp');
Route::get('/communication', function () {
    return view('communication');
})->name('communication');
// Route::post('/template/store', [TemplateMasterController::class, 'sendEmail'])->name('template.store');
Route::post('/template/store', [TemplateMasterController::class, 'store'])->name('template.store');

Route::post('/send-otp', [LoginController::class, 'sendOtp'])->name('send.otp');
Route::post('/verify-otp', [LoginController::class, 'verifyOtp'])->name('verify.otp');
Route::get('/otp-verify', [LoginController::class, 'otpVerifyPage'])->name('otpVerify.page');
Route::post('/resend-otp', [LoginController::class, 'resendOtp'])->name('resend.otp');

Route::get('statusList', [StatusMasterController::class, 'index'])->name('statusList');
Route::get('createFaq', [FaqController::class, 'index'])->name('createFaq');
Route::get('createTag', [TagNameController::class, 'index'])->name('createTag');
Route::get('qualification', [QualificationMasterController::class, 'index'])->name('qualification');
Route::get('createCta', [CtaMasterController::class, 'createCta'])->name('createCta');

Route::get('createOem', [OemMasterController::class, 'index'])->name('createOem');

// Logs Api

Route::get('LogsApiList', [LogsApiController::class, 'LogsApiList'])->name('LogsApiList');
Route::get('/key-utility/{id}/edit', [KeyUtilityController::class, 'edit']);
Route::resource('MaskData', MaskDataController::class);

