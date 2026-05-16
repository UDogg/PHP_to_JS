<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('otps_master', function (Blueprint $table) {
            if(!Schema::hasColumn('otps_master','otp_validation_time')) {
                $table->integer('otp_validation_time')->change();
            }

            if(!Schema::hasColumn('otps_master','resend_otp_time')) {
                $table->integer('resend_otp_time')->change();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('otps_master', function (Blueprint $table) {
            $table->time('otp_validation_time')->change();
            $table->time('resend_otp_time')->change();
        });
    }
};
