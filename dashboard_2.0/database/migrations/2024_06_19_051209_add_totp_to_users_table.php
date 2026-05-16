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

            Schema::table('users', function (Blueprint $table) {
                if(!Schema::hasColumn('users', 'username'))
                {
                $table->string('username');
                }
                if(!Schema::hasColumn('users', 'mobile'))
                {
                $table->string('mobile');
                }
                if(!Schema::hasColumn('users', 'address'))
                {
                $table->string('address');
                }
                if(!Schema::hasColumn('users', 'pincode'))
                {
                $table->string('pincode');
                }
                if(!Schema::hasColumn('users', 'gender'))
                {
                $table->enum('gender', ['M', 'F']);
                }
                if(!Schema::hasColumn('users', 'otp_expires_in'))
                {
                $table->integer('otp_expires_in')->nullable();
                }
                if(!Schema::hasColumn('users', 'otp_expires_at'))
                {
                $table->timestamp('otp_expires_at')->nullable();
                }
                if(!Schema::hasColumn('users', 'totp_secret'))
                {
                $table->string('totp_secret')->nullable();
                }
                if(!Schema::hasColumn('users', 'status'))
                {
                $table->enum('status', ['Y', 'N']);
                }

            });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('users', function (Blueprint $table) {
            //
        });
    }
};
