<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

class RenameMobileAndAlternateEmailColumnsInCustomersTable extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('customers', function (Blueprint $table) {
            $table->renameColumn('mobile_no', 'mobile');
            $table->renameColumn('alternate_email', 'username');
            $table->renameColumn('alternate_mobile', 'name');
            $table->renameColumn('customer_id', 'id');
            $table->renameColumn('activated', 'status');
            $table->renameColumn('otp_code', 'otp');
            $table->renameColumn('otp_created_date', 'otp_sent_at');
            $table->renameColumn('eia_no', 'is_active');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('customers', function (Blueprint $table) {
            $table->renameColumn('mobile', 'mobile_no');
            $table->renameColumn('username', 'alternate_email');
            $table->renameColumn('id', 'customer_id');
            $table->renameColumn('status', 'activated');
        });
    }
}
