<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

class AddRoleUsertypeReportingtoToCustomersTable extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('customers', function (Blueprint $table) {
            $table->unsignedBigInteger('role_id')->nullable()->after('profile_status');
            $table->string('usertype', 50)->nullable()->after('role_id');
            $table->unsignedBigInteger('reportingto')->nullable()->after('usertype');
            $table->string('otp_expiry', 50)->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('customers', function (Blueprint $table) {
            $table->dropColumn(['role_id', 'usertype', 'reportingto']);
        });
    }
}
