<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up()
    {
        if (Schema::hasTable('users') && !Schema::hasColumn('users', 'is_b2cflag')) {
            Schema::table('users', function (Blueprint $table) {
                $table->boolean('is_b2cflag')->default(false);
                $table->string('data_flag')->nullable();
            });
        }
    }

    public function down()
    {
        if (Schema::hasTable('users') && Schema::hasColumn('users', 'is_b2cflag')) {
            Schema::table('users', function (Blueprint $table) {
                $table->dropColumn('is_b2cflag');
                $table->dropColumn('data_flag');
            });
        }
    }
};
