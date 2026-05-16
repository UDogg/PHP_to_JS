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
        //
        if(Schema::hasTable('users'))
        {
//            user bank details and nominee detials
            Schema::table('users', function (Blueprint $table) {
                $table->string('bank_branch')->nullable();
                $table->string('bank_city')->nullable();
                $table->string('bank_name')->nullable();
                $table->string('account_no')->nullable();
                $table->string('ifsc_code')->nullable();
                $table->string('account_holder_name')->nullable();
                $table->string('nominee_first_name')->nullable();
                $table->string('nominee_last_name')->nullable();
                $table->string('nominee_middle_name')->nullable();
                $table->string('nominee_relation')->nullable();
                $table->string('nominee_dob')->nullable();
                $table->string('nominee_mobile')->nullable();
                $table->string('nominee_email')->nullable();
                $table->string('reportingto')->nullable();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
    }
};
